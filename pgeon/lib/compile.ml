(* Debug formatting *)

let string_of_term t =
  if Log.get_level () > Log.Debug then ""
  else
    let rec string_of_term = function
      | Term.Bvar i -> Printf.sprintf "#%d" i
      | Term.Fvar x -> "'" ^ x
      | Term.Mvar x -> "?" ^ x
      | Term.App (f, []) -> f
      | Term.App (f, args) ->
          Printf.sprintf "%s(%s)" f
            (String.concat ", " (List.map string_of_term args))
      | Term.Bind (b, body) -> Printf.sprintf "%s.(%s)" b (string_of_term body)
    in
    string_of_term t

let string_of_free_subst (Term.FreeSubstitution subst) =
  if Log.get_level () > Log.Debug then ""
  else
    let items =
      subst
      |> List.map (fun (x, t) -> Printf.sprintf "%s <- %s" x (string_of_term t))
    in
    "{ " ^ String.concat ", " items ^ " }"

let string_of_formula (id, t) =
  if Log.get_level () > Log.Debug then ""
  else Printf.sprintf "%d:%s" id (string_of_term t)

let string_of_branch br =
  if Log.get_level () > Log.Debug then ""
  else "[" ^ String.concat " ; " (List.map string_of_formula br) ^ "]"

let string_of_tree tree =
  if Log.get_level () > Log.Debug then ""
  else
    String.concat "\n"
      (List.mapi
         (fun i br -> Printf.sprintf "  branch %d = %s" i (string_of_branch br))
         tree)

(* AST-to-term compilation and instantiation *)

let term_of_expr expr =
  let rec compile env = function
    | Ast.EVar v -> (
        match Compat.find_index (( = ) v) env with
        | Some i -> Term.Bvar i
        | None ->
            if String.capitalize_ascii v = v then Term.Mvar v
            else Term.App (v, []))
    | Ast.EApp (f, args) -> Term.App (f, List.map (compile env) args)
    | Ast.EBind (b, v, body) -> Term.Bind (b, compile (v :: env) body)
  in
  compile [] expr

let free_substitute_tree theta (tree : Tableau.proof_tree) : Tableau.proof_tree
    =
  List.map (List.map (fun (id, t) -> (id, Term.free_substitute theta t))) tree

let _meta_substitute_tree subst (tree : Tableau.proof_tree) : Tableau.proof_tree
    =
  List.map (List.map (fun (id, t) -> (id, Term.substitute subst t))) tree

type rule_env = (string * Term.t) list
type branch_env = (string * Tableau.formula list) list
type tree_env = (string * Tableau.proof_tree) list

let branch_tail_name = function
  | Ast.TailAny name | Ast.TailMapped (_, name) -> name

let instantiate_rule_expr lhs_subst (env : rule_env) (expr : Ast.expr) =
  let rec go : Ast.expr -> Term.t = function
    | EVar v -> (
        match List.assoc_opt v env with
        | Some t -> t
        | None -> Term.substitute lhs_subst (Term.Mvar v))
    | EApp (f, args) -> Term.App (f, List.map go args)
    | t (* EBind *) ->
        let rec compile env_names : Ast.expr -> Term.t = function
          | EVar x -> (
              match Compat.find_index (( = ) x) env_names with
              | Some i -> Term.Bvar i
              | None -> (
                  match List.assoc_opt x env with
                  | Some t -> t
                  | None -> Term.substitute lhs_subst (Term.Mvar x)))
          | EApp (f, args) -> Term.App (f, List.map (compile env_names) args)
          | EBind (b, x, body) -> Term.Bind (b, compile (x :: env_names) body)
        in
        compile [] t
  in
  go expr

let instantiate_rule_expr_from_term lhs_subst (env : rule_env) t =
  let rec go = function
    | Term.Bvar _ as t -> t
    | Term.Fvar _ as t -> t
    | Term.Mvar v -> (
        match List.assoc_opt v env with
        | Some t -> t
        | None -> Term.substitute lhs_subst (Term.Mvar v))
    | Term.App (f, args) -> Term.App (f, List.map go args)
    | Term.Bind (b, body) -> Term.Bind (b, go body)
  in
  go t

(* Where clauses *)

let eval_where_op runtime st lhs_subst env src_term = function
  | Ast.WhereSubstGen { bound = _; by } -> (
      match (Registry.find_generator runtime by.name) st src_term with
      | None -> None
      | Some (generated, st') ->
          let result = Term.var_open src_term generated in
          Some (st', result))
  | Ast.WhereUnifier { name; left; right } -> (
      let left_t = instantiate_rule_expr lhs_subst env left in
      let right_t = instantiate_rule_expr lhs_subst env right in
      match (Registry.find_unifier runtime name) left_t right_t with
      | None -> None
      | Some theta ->
          let result = Term.free_substitute theta src_term in
          Some (st, result))

let add_terms_to_branch start_id terms branch =
  let rec aux next_id acc = function
    | [] -> (List.rev acc @ branch, next_id)
    | t :: tl -> aux (next_id + 1) ((next_id, t) :: acc) tl
  in
  aux start_id [] terms

let instantiate_branch_expr subst env branch_env next_formula_id
    ((exprs, tails) : Ast.branch_expr) =
  let base_branch =
    let rec collect acc = function
      | [] -> Some (List.concat (List.rev acc))
      | tail :: tl -> (
          match List.assoc_opt (branch_tail_name tail) branch_env with
          | None -> None
          | Some branch -> collect (branch :: acc) tl)
    in
    collect [] tails
  in
  match base_branch with
  | None -> None
  | Some base_branch ->
      let terms = List.map (instantiate_rule_expr subst env) exprs in
      let branch, next_formula_id =
        add_terms_to_branch next_formula_id terms base_branch
      in
      Some (branch, next_formula_id)

let pattern_matches pattern term =
  let rec go subst pattern term =
    match pattern with
    | Term.Mvar "_" -> Some subst
    | Term.Mvar m -> (
        match List.assoc_opt m subst with
        | None -> Some ((m, term) :: subst)
        | Some bound -> if bound = term then Some subst else None)
    | Term.Bvar i -> (
        match term with Term.Bvar j when i = j -> Some subst | _ -> None)
    | Term.Fvar x -> (
        match term with Term.Fvar y when x = y -> Some subst | _ -> None)
    | Term.App (f, ps) -> (
        match term with
        | Term.App (g, ts) when f = g && List.length ps = List.length ts ->
            List.fold_left2
              (fun acc p t -> Option.bind acc (fun subst -> go subst p t))
              (Some subst) ps ts
        | _ -> None)
    | Term.Bind (b, p) -> (
        match term with
        | Term.Bind (b', t) when b = b' -> go subst p t
        | _ -> None)
  in
  Option.is_some (go [] pattern term)

let rec where_pattern_matches lhs_subst env pattern term =
  match pattern with
  | Ast.WherePatternExpr expr ->
      let pattern = instantiate_rule_expr lhs_subst env expr in
      pattern_matches pattern term
  | Ast.WherePatternNot pattern ->
      not (where_pattern_matches lhs_subst env pattern term)

let instantiate_tree_expr subst env branch_env tree_env next_formula_id
    ((branches, tree_tail) : Ast.tree_expr) =
  match List.assoc_opt tree_tail tree_env with
  | None -> None
  | Some tail_tree ->
      let rec aux next_formula_id acc = function
        | [] -> Some (List.rev acc @ tail_tree, next_formula_id)
        | br :: tl -> (
            match
              instantiate_branch_expr subst env branch_env next_formula_id br
            with
            | None -> None
            | Some (branch, next_formula_id') ->
                aux next_formula_id' (branch :: acc) tl)
      in
      aux next_formula_id [] branches

let eval_where_expr_clause runtime st lhs_subst (env : rule_env)
    (branch_env : branch_env) (tree_env : tree_env) = function
  | Ast.WhereExprClause { dst; src; op } ->
      let src_term = instantiate_rule_expr lhs_subst env src in
      eval_where_op runtime st lhs_subst env src_term op
      |> Option.map (fun (st', result) ->
          (st', (dst, result) :: env, branch_env, tree_env))
  | Ast.WhereTreeClause { dst; src; op } -> (
      match
        instantiate_tree_expr lhs_subst env branch_env tree_env
          st.next_formula_id src
      with
      | None -> None
      | Some (src_tree, _) -> (
          match op with
          | Ast.WhereSubstGen _ ->
              failwith "Tree generation not supported in where clauses"
          | Ast.WhereUnifier { name; left; right } -> (
              let left_t = instantiate_rule_expr lhs_subst env left in
              let right_t = instantiate_rule_expr lhs_subst env right in
              match (Registry.find_unifier runtime name) left_t right_t with
              | None -> None
              | Some theta ->
                  let result_tree = free_substitute_tree theta src_tree in
                  Log.debug
                    "TREE WHERE %s\nsrc_tree=\n%s\ntheta=%s\nresult_tree=\n%s\n"
                    dst (string_of_tree src_tree)
                    (string_of_free_subst theta)
                    (string_of_tree result_tree);
                  Some (st, env, branch_env, (dst, result_tree) :: tree_env))))
  | Ast.WhereBranchAllMatch { branch; pattern } -> (
      match List.assoc_opt branch branch_env with
      | None -> None
      | Some formulas ->
          if
            List.for_all
              (fun (_, term) ->
                where_pattern_matches lhs_subst env pattern term)
              formulas
          then Some (st, env, branch_env, tree_env)
          else None)

let eval_where_clauses (reg : Registry.t) st
    (lhs_subst : Term.meta_substitution) (branch_env : branch_env)
    (tree_env : tree_env) clauses =
  let rec go st env branch_env tree_env = function
    | [] -> Some (st, env, branch_env, tree_env)
    | clause :: tl -> (
        match
          eval_where_expr_clause reg st lhs_subst env branch_env tree_env clause
        with
        | None -> None
        | Some (st', env', branch_env', tree_env') ->
            go st' env' branch_env' tree_env' tl)
  in
  go st [] branch_env tree_env clauses

(* Rule compilation *)

let cache_key (rule_id : int) (candidate : Tableau.formula list)
    (branch : Tableau.formula list) =
  ( rule_id,
    List.map snd candidate,
    branch |> List.map snd |> List.sort_uniq compare )

let cache_check enabled cache key = enabled && List.mem key cache

let cache_insert enabled cache key =
  if cache_check enabled cache key then cache
  else if enabled then key :: cache
  else cache

let singleton_or_empty = function None -> Seq.empty | Some st -> Seq.return st

let rec invertible_bang run_once matched st =
  let nexts = run_once st in
  match nexts () with
  | Seq.Nil -> if matched then Seq.return st else Seq.empty
  | Seq.Cons (st', rest) ->
      Seq.cons st' rest
      |> Seq.map (invertible_bang run_once true)
      |> Utils.diagonal

let compile_rule ~use_history (reg : Registry.t) id (decl : Ast.rule_decl) :
    Tableau.rule =
  let build_branches start_id base_branch rhs_branches =
    match rhs_branches with
    | [] -> ([ base_branch ], start_id)
    | _ ->
        let rec aux next_id acc = function
          | [] -> (List.rev acc, next_id)
          | rhs_branch :: tl ->
              let new_branch, next_id' =
                add_terms_to_branch next_id rhs_branch base_branch
              in
              aux next_id' (new_branch :: acc) tl
        in
        aux start_id [] rhs_branches
  in
  let generate_candidates_branch_rules (t : Tableau.proof_tree) (arity : int) =
    t |> List.to_seq
    |> Compat.seq_mapi (fun branch_idx branch -> (branch_idx, branch))
    |> Seq.flat_map (fun (branch_idx, branch) ->
        Utils.perm arity branch |> List.to_seq
        |> Seq.map (fun candidate ->
            let candidate_ids = List.map fst candidate in
            let rest_branch =
              List.filter
                (fun (formula_id, _) -> not (List.mem formula_id candidate_ids))
                branch
            in
            let rest_tree =
              t
              |> List.mapi (fun i br -> (i, br))
              |> List.filter (fun (i, _) -> i <> branch_idx)
              |> List.map snd
            in
            (rest_tree, branch, rest_branch, candidate)))
  in
  let generate_candidates_tree_rules (t : Tableau.proof_tree)
      (lhs_branches : Ast.branch_expr list) =
    let indexed_tree = List.mapi (fun i branch -> (i, branch)) t in
    let rec choose_formulas acc = function
      | [], [] -> Seq.return (List.rev acc)
      | (_, branch) :: branch_tl, ((exprs, _) as lhs_branch) :: lhs_tl ->
          let arity = List.length exprs in
          Utils.perm arity branch |> List.to_seq
          |> Seq.map (fun candidate ->
              let candidate_ids = List.map fst candidate in
              let rest_branch =
                List.filter
                  (fun (formula_id, _) ->
                    not (List.mem formula_id candidate_ids))
                  branch
              in
              (lhs_branch, rest_branch, candidate))
          |> Seq.flat_map (fun matched ->
              choose_formulas (matched :: acc) (branch_tl, lhs_tl))
      | _ -> Seq.empty
    in
    Utils.perm (List.length lhs_branches) indexed_tree
    |> List.to_seq
    |> Seq.flat_map (fun selected_branches ->
        let selected_ids = List.map fst selected_branches in
        let rest_tree =
          indexed_tree
          |> List.filter (fun (i, _) -> not (List.mem i selected_ids))
          |> List.map snd
        in
        choose_formulas [] (selected_branches, lhs_branches)
        |> Seq.map (fun matched_branches -> (rest_tree, matched_branches)))
  in
  let tail_accepts tail formulas =
    match tail with
    | Ast.TailAny _ -> true
    | Ast.TailMapped (f, _) ->
        List.for_all
          (function _, Term.App (g, [ _ ]) -> f = g | _ -> false)
          formulas
  in
  let partition_branch_remainder tails formulas =
    let tail_count = List.length tails in
    let empty_groups = List.init tail_count (fun _ -> []) in
    let add_to_group idx formula groups =
      groups
      |> List.mapi (fun i group -> if i = idx then formula :: group else group)
    in
    match tails with
    | [] -> if formulas = [] then Seq.return [] else Seq.empty
    | [ tail ] ->
        if tail_accepts tail formulas then
          Seq.return [ (branch_tail_name tail, formulas) ]
        else Seq.empty
    | _ ->
        let rec assign_all groups = function
          | [] ->
              let groups = List.map List.rev groups in
              if List.for_all2 tail_accepts tails groups then
                Seq.return
                  (List.map2
                     (fun tail formulas -> (branch_tail_name tail, formulas))
                     tails groups)
              else Seq.empty
          | formula :: tl ->
              List.init tail_count Fun.id
              |> List.to_seq
              |> Seq.flat_map (fun idx ->
                  assign_all (add_to_group idx formula groups) tl)
        in
        assign_all empty_groups formulas
  in
  let branch_env_choices matched_branches =
    let rec loop acc = function
      | [] -> Seq.return (List.concat (List.rev acc))
      | ((_, tails), rest_branch, _) :: tl ->
          partition_branch_remainder tails rest_branch
          |> Seq.flat_map (fun env -> loop (env :: acc) tl)
    in
    loop [] matched_branches
  in
  match decl with
  | Ast.RuleBranch { arrow; lhs; rhs; where; name } ->
      let lhs_terms = List.map term_of_expr lhs in
      let rhs_termss = List.map (List.map term_of_expr) rhs in
      let arity = List.length lhs_terms in
      let candidate_rest branch candidate =
        let candidate_ids = List.map fst candidate in
        List.filter
          (fun (formula_id, _) -> not (List.mem formula_id candidate_ids))
          branch
      in
      let apply_branch_candidate (st : Tableau.proof_state) rest_branch
          candidate =
        let candidate_terms = List.map snd candidate in
        let key = cache_key id candidate (candidate @ rest_branch) in
        if cache_check use_history st.applied key then None
        else
          match Term.match_terms candidate_terms lhs_terms with
          | None -> None
          | Some lhs_subst -> (
              Log.debug "RULE %s matched\ncandidate=%s\nrest_branch=%s\n" name
                (string_of_branch candidate)
                (string_of_branch rest_branch);
              match eval_where_clauses reg st lhs_subst [] [] where with
              | None ->
                  Log.debug "RULE %s: where clauses failed\n" name;
                  None
              | Some (st, env, _, _) -> (
                  let rhs_instantiated =
                    List.map
                      (List.map (instantiate_rule_expr_from_term lhs_subst env))
                      rhs_termss
                  in
                  match arrow with
                  | Ast.Close ->
                      Log.debug "CLOSE by rule %s on candidate=%s\n" name
                        (string_of_branch candidate);
                      Some (st, [])
                  | Ast.Invertible ->
                      let new_branches, next_formula_id =
                        build_branches st.next_formula_id rest_branch
                          rhs_instantiated
                      in
                      Log.debug "INVERTIBLE rule %s applied on candidate=%s\n"
                        name
                        (string_of_branch candidate);
                      Some
                        ( {
                            st with
                            next_formula_id;
                            applied = cache_insert use_history st.applied key;
                          },
                          new_branches )
                  | Ast.NonInvertible ->
                      let base_branch = candidate @ rest_branch in
                      let new_branches, next_formula_id =
                        build_branches st.next_formula_id base_branch
                          rhs_instantiated
                      in
                      Log.debug
                        "NON-INVERTIBLE rule %s applied on candidate=%s\n" name
                        (string_of_branch candidate);
                      Some
                        ( {
                            st with
                            next_formula_id;
                            applied = cache_insert use_history st.applied key;
                          },
                          new_branches )))
      in
      {
        id;
        run =
          (fun st ->
            generate_candidates_branch_rules st.tree arity
            |> Seq.filter_map
                 (fun (rest_tree, _branch, rest_branch, candidate) ->
                   match apply_branch_candidate st rest_branch candidate with
                   | None -> None
                   | Some (st, branches) ->
                       Some { st with tree = branches @ rest_tree }));
        run_bang =
          (match arrow with
          | Ast.Invertible ->
              Some
                (fun st ->
                  invertible_bang
                    (fun (st : Tableau.proof_state) ->
                      generate_candidates_branch_rules st.tree arity
                      |> Seq.filter_map
                           (fun (rest_tree, _branch, rest_branch, candidate) ->
                             match
                               apply_branch_candidate st rest_branch candidate
                             with
                             | None -> None
                             | Some (st, branches) ->
                                 Some { st with tree = branches @ rest_tree }))
                    false st)
          | Ast.Close ->
              Some
                (fun st ->
                  let first_application (st : Tableau.proof_state) =
                    generate_candidates_branch_rules st.tree arity
                    |> Seq.filter_map
                         (fun (rest_tree, _branch, rest_branch, candidate) ->
                           match
                             apply_branch_candidate st rest_branch candidate
                           with
                           | None -> None
                           | Some (st, branches) ->
                               Some { st with tree = branches @ rest_tree })
                    |> Compat.seq_uncons |> Option.map fst
                  in
                  let rec loop matched st =
                    match first_application st with
                    | None -> if matched then Some st else None
                    | Some st -> loop true st
                  in
                  singleton_or_empty (loop false st))
          | Ast.NonInvertible ->
              Some
                (fun st ->
                  let rec process_candidates branch st matched acc = function
                    | [] -> (st, matched, List.rev acc)
                    | candidate :: tl -> (
                        let rest_branch = candidate_rest branch candidate in
                        match
                          apply_branch_candidate st rest_branch candidate
                        with
                        | None -> process_candidates branch st matched acc tl
                        | Some (st, branches) ->
                            process_candidates branch st true
                              (List.rev_append branches acc)
                              tl)
                  in
                  let rec process_branches (st : Tableau.proof_state) matched
                      acc = function
                    | [] ->
                        if matched then Some { st with tree = List.rev acc }
                        else None
                    | branch :: tl ->
                        let candidates = Utils.perm arity branch in
                        let st, branch_matched, branches =
                          process_candidates branch st false [] candidates
                        in
                        let matched = matched || branch_matched in
                        let branches =
                          if branch_matched then branches else [ branch ]
                        in
                        process_branches st matched
                          (List.rev_append branches acc)
                          tl
                  in
                  singleton_or_empty (process_branches st false [] st.tree)));
      }
  | Ast.RuleTree { arrow; lhs = lhs_branches, lhs_tree_tail; rhs; where; name }
    ->
      let run_tree (st : Tableau.proof_state) =
        generate_candidates_tree_rules st.tree lhs_branches
        |> Seq.flat_map (fun (rest_tree, matched_branches) ->
            let candidate_terms =
              matched_branches
              |> List.concat_map (fun (_, _, candidate) ->
                  List.map snd candidate)
            in
            let tree_context =
              matched_branches
              |> List.concat_map (fun (_, _, branch) -> List.map snd branch)
              |> List.sort_uniq compare
            in
            let key = (id, candidate_terms, tree_context) in
            if cache_check use_history st.applied key then Seq.empty
            else
              let lhs_terms =
                matched_branches
                |> List.concat_map (fun ((exprs, _), _, _) ->
                    List.map term_of_expr exprs)
              in
              match Term.match_terms candidate_terms lhs_terms with
              | None -> Seq.empty
              | Some subst ->
                  branch_env_choices matched_branches
                  |> Seq.filter_map (fun branch_env ->
                      let tree_env = [ (lhs_tree_tail, rest_tree) ] in
                      match
                        eval_where_clauses reg st subst branch_env tree_env
                          where
                      with
                      | None -> None
                      | Some (st, env, branch_env, tree_env) -> (
                          match
                            instantiate_tree_expr subst env branch_env tree_env
                              st.next_formula_id rhs
                          with
                          | None -> None
                          | Some (tree, next_formula_id) ->
                              Log.debug
                                "TREE RULE %s succeeded\nnew_tree=\n%s\n" name
                                (string_of_tree tree);
                              Some
                                {
                                  st with
                                  tree;
                                  next_formula_id;
                                  applied =
                                    cache_insert use_history st.applied key;
                                })))
      in
      {
        id;
        run = run_tree;
        run_bang =
          (match arrow with
          | Ast.Invertible -> Some (fun st -> invertible_bang run_tree false st)
          | Ast.Close | Ast.NonInvertible ->
              Some
                (fun st ->
                  let rec loop matched st =
                    match Compat.seq_uncons (run_tree st) with
                    | None -> if matched then Some st else None
                    | Some (st, _) -> loop true st
                  in
                  singleton_or_empty (loop false st)));
      }

(* Strategy compilation and initial proof state *)

let compile ?(focused = false) ?(branch_obligations = false)
    ?(phase_scheduling = false) (reg : Registry.t) (logic : Ast.logic_decl)
    (problem : Ast.problem_decl) =
  let branch_obligations = focused || branch_obligations in
  let phase_scheduling = focused || phase_scheduling in
  let use_history = branch_obligations && phase_scheduling in
  let compiled_rule_entries =
    logic.rules
    |> List.mapi (fun id rule ->
        let name =
          match rule with
          | Ast.RuleBranch { name; _ } -> name
          | Ast.RuleTree { name; _ } -> name
        in
        let arrow =
          match rule with
          | Ast.RuleBranch { arrow; _ } -> arrow
          | Ast.RuleTree { arrow; _ } -> arrow
        in
        (name, arrow, compile_rule ~use_history reg id rule))
  in
  let compiled_rules =
    List.map (fun (name, _, rule) -> (name, rule)) compiled_rule_entries
  in
  let rec compile_strategy = function
    | Ast.SCall name -> (
        match List.assoc_opt name compiled_rules with
        | Some rule -> Tableau.applyRule rule
        | None -> (
            let decl =
              List.find_opt
                (fun (s : Ast.strategy_decl) -> s.name = name)
                logic.strategies
            in
            match decl with
            | Some s -> compile_strategy s.body
            | None ->
                invalid_arg (Printf.sprintf "Unknown strategy or rule: %s" name)
            ))
    | Ast.SBang name -> (
        match List.assoc_opt name compiled_rules with
        | Some rule -> Tableau.applyRuleBang rule
        | None -> invalid_arg (Printf.sprintf "Unknown rule: %s" name))
    | Ast.SOrElse (s1, s2) ->
        Tableau.orElse (compile_strategy s1) (compile_strategy s2)
    | Ast.SAndThen (s1, s2) ->
        Tableau.andThen (compile_strategy s1) (compile_strategy s2)
    | Ast.SOrAlt (s1, s2) ->
        Tableau.orAlt (compile_strategy s1) (compile_strategy s2)
    | Ast.SAndAlt (s1, s2) ->
        Tableau.andAlt (compile_strategy s1) (compile_strategy s2)
    | Ast.SRepeat s -> Tableau.repeat (compile_strategy s)
    | Ast.SOptional s -> Tableau.optional (compile_strategy s)
  in
  let initial_branch =
    problem.formulas |> List.mapi (fun id expr -> (id, term_of_expr expr))
  in
  let initial_state : Tableau.proof_state =
    {
      tree = [ initial_branch ];
      next_fresh = 0;
      next_symbol = 0;
      next_formula_id = List.length problem.formulas;
      applied = [];
    }
  in
  let branch_strategy =
    let module Key = struct
      type t = Term.t list * Tableau.application_key list * int * int

      let equal = ( = )
      let hash = Hashtbl.hash
    end in
    let module Cache = Hashtbl.Make (Key) in
    let module Active = Set.Make (struct
      type t = Key.t

      let compare = compare
    end) in
    let cache = Cache.create 100_003 in
    let iterations = ref 0 in
    let step_expr =
      match logic.entry_strategy.body with
      | Ast.SRepeat body -> body
      | body -> body
    in
    let step = compile_strategy step_expr in
    let canonical_history history = List.sort_uniq compare history in
    let canonical_branch branch =
      branch
      |> List.sort (fun (_, left) (_, right) -> compare left right)
      |> List.sort_uniq (fun (_, left) (_, right) -> compare left right)
    in
    let key_of branch history st =
      ( canonical_branch branch |> List.map snd,
        canonical_history history,
        st.Tableau.next_fresh,
        st.Tableau.next_symbol )
    in
    let rec solve_branch active branch history st =
      let branch = canonical_branch branch in
      let key = key_of branch history st in
      if Cache.mem cache key || Active.mem key active then Seq.empty
      else
        let active = Active.add key active in
        incr iterations;
        let results =
          step { st with Tableau.tree = [ branch ]; applied = history }
          |> Seq.flat_map (fun next ->
              solve_children active next.Tableau.tree next.applied next)
        in
        match Compat.seq_uncons results with
        | None ->
            Cache.replace cache key ();
            Seq.empty
        | Some (result, rest) -> Seq.cons result rest
    and solve_children active branches history st =
      match branches with
      | [] -> Seq.return { st with Tableau.tree = []; applied = history }
      | branch :: tl ->
          solve_branch active branch history st
          |> Seq.flat_map (fun st' -> solve_children active tl history st')
    in
    fun st ->
      Cache.clear cache;
      iterations := 0;
      match
        Compat.seq_uncons
          (solve_children Active.empty st.Tableau.tree st.applied st)
      with
      | None ->
          Log.info "branch iterations=%d cache=%d" !iterations
            (Cache.length cache);
          Seq.empty
      | Some (st', rest) ->
          Log.info "branch iterations=%d cache=%d" !iterations
            (Cache.length cache);
          Seq.cons { st' with Tableau.tree = [] } rest
  in
  let focused_strategy =
    let module Key = struct
      type t = Term.t list list * Tableau.application_key list * int * int

      let equal = ( = )
      let hash = Hashtbl.hash
    end in
    let module Cache = Hashtbl.Make (Key) in
    let module Active = Set.Make (struct
      type t = Key.t

      let compare = compare
    end) in
    let cache = Cache.create 100_003 in
    let applications = ref 0 in
    let rule_names =
      logic.rules
      |> List.map (function
        | Ast.RuleBranch { name; _ } -> name
        | Ast.RuleTree { name; _ } -> name)
    in
    let rec collect_rules seen_strategies acc = function
      | Ast.SCall name | Ast.SBang name -> (
          if List.mem name rule_names then name :: acc
          else if List.mem name seen_strategies then acc
          else
            match
              List.find_opt
                (fun (decl : Ast.strategy_decl) -> decl.name = name)
                logic.strategies
            with
            | None -> acc
            | Some decl -> collect_rules (name :: seen_strategies) acc decl.body
          )
      | Ast.SOrElse (left, right)
      | Ast.SAndThen (left, right)
      | Ast.SOrAlt (left, right)
      | Ast.SAndAlt (left, right) ->
          collect_rules seen_strategies
            (collect_rules seen_strategies acc left)
            right
      | Ast.SRepeat body | Ast.SOptional body ->
          collect_rules seen_strategies acc body
    in
    let reachable_rules =
      collect_rules [] [] logic.entry_strategy.body |> List.sort_uniq compare
    in
    let rec direct_rule_calls acc = function
      | Ast.SCall name | Ast.SBang name -> (
          if List.mem name rule_names then name :: acc
          else
            match
              List.find_opt
                (fun (decl : Ast.strategy_decl) -> decl.name = name)
                logic.strategies
            with
            | None -> acc
            | Some decl -> direct_rule_calls acc decl.body)
      | Ast.SOrElse (left, right)
      | Ast.SAndThen (left, right)
      | Ast.SOrAlt (left, right)
      | Ast.SAndAlt (left, right) ->
          direct_rule_calls (direct_rule_calls acc left) right
      | Ast.SRepeat body | Ast.SOptional body -> direct_rule_calls acc body
    in
    let rule_entry name =
      List.find_opt
        (fun (candidate, _, _) -> candidate = name)
        compiled_rule_entries
    in
    let post_phases =
      logic.strategies
      |> List.filter_map (fun (decl : Ast.strategy_decl) ->
          match decl.body with
          | Ast.SAndThen (Ast.SCall first, post) -> (
              match rule_entry first with
              | Some (_, Ast.NonInvertible, rule) ->
                  let post_names =
                    direct_rule_calls [] post |> List.sort_uniq compare
                  in
                  let post_rules =
                    post_names
                    |> List.filter_map (fun name ->
                        match rule_entry name with
                        | Some (_, _, post_rule) -> Some post_rule
                        | None -> None)
                  in
                  Some (rule.Tableau.id, post_rules, post_names)
              | _ -> None)
          | _ -> None)
    in
    let post_rule_names =
      post_phases
      |> List.concat_map (fun (_, _, names) -> names)
      |> List.sort_uniq compare
    in
    let canonical_history history = List.sort_uniq compare history in
    let canonical_branch branch =
      branch
      |> List.sort (fun (_, left) (_, right) -> compare left right)
      |> List.sort_uniq (fun (_, left) (_, right) -> compare left right)
    in
    let key_of_branch branch history st =
      ( [ canonical_branch branch |> List.map snd ],
        canonical_history history,
        st.Tableau.next_fresh,
        st.Tableau.next_symbol )
    in
    let canonical_tree tree =
      tree |> List.map canonical_branch
      |> List.sort (fun left right ->
          compare (List.map snd left) (List.map snd right))
    in
    let key_of_tree tree history st =
      ( canonical_tree tree |> List.map (List.map snd),
        canonical_history history,
        st.Tableau.next_fresh,
        st.Tableau.next_symbol )
    in
    let rules_of_kind kind =
      compiled_rule_entries
      |> List.filter_map (fun (name, arrow, rule) ->
          if
            arrow = kind
            && List.mem name reachable_rules
            && not (List.mem name post_rule_names)
          then Some rule
          else None)
    in
    let closing_rules = rules_of_kind Ast.Close in
    let invertible_rules = rules_of_kind Ast.Invertible in
    let noninvertible_rules = rules_of_kind Ast.NonInvertible in
    let run_rule rule branch history st =
      incr applications;
      rule.Tableau.run { st with Tableau.tree = [ branch ]; applied = history }
    in
    let first_result rules branch history st =
      let rec loop = function
        | [] -> None
        | rule :: tl -> (
            match Compat.seq_uncons (run_rule rule branch history st) with
            | None -> loop tl
            | Some (result, _) -> Some result)
      in
      loop rules
    in
    let rec solve_branch active branch history st =
      let branch = canonical_branch branch in
      let key = key_of_branch branch history st in
      match Cache.find_opt cache key with
      | Some true -> Some { st with Tableau.tree = []; applied = history }
      | Some false -> None
      | None when Active.mem key active -> None
      | None -> (
          let active = Active.add key active in
          let finish result =
            Cache.replace cache key (Option.is_some result);
            result
          in
          let rec try_closing = function
            | [] -> None
            | rule :: tl ->
                let results = run_rule rule branch history st in
                if
                  Compat.seq_exists
                    (fun result -> Tableau.is_closed result.Tableau.tree)
                    results
                then Some { st with Tableau.tree = []; applied = history }
                else try_closing tl
          in
          match try_closing closing_rules with
          | Some result -> finish (Some result)
          | None -> (
              match first_result invertible_rules branch history st with
              | Some next ->
                  finish
                    (solve_children active next.Tableau.tree next.applied next)
              | None ->
                  finish
                    (try_noninvertible active branch history st
                       noninvertible_rules)))
    and solve_children active branches history st =
      match branches with
      | [] -> Some { st with Tableau.tree = []; applied = history }
      | branch :: tl -> (
          match solve_branch active branch history st with
          | None -> None
          | Some st' -> solve_children active tl history st')
    and apply_post_rules rules branches history st =
      let rec normalize_branch branch history st =
        match first_result rules branch history st with
        | None -> Some ([ branch ], history, st)
        | Some next -> normalize_children next.Tableau.tree next.applied next
      and normalize_children branches history st =
        match branches with
        | [] -> Some ([], history, st)
        | branch :: tl -> (
            match normalize_branch branch history st with
            | None -> None
            | Some (normalized, _, st') -> (
                match normalize_children tl history st' with
                | None -> None
                | Some (rest, _, st'') -> Some (normalized @ rest, history, st'')
                ))
      in
      let rec normalize_all acc branches st =
        match branches with
        | [] -> Some (List.rev acc, history, st)
        | branch :: tl -> (
            match normalize_branch branch history st with
            | None -> None
            | Some (normalized, _, st') ->
                normalize_all (List.rev_append normalized acc) tl st')
      in
      normalize_all [] branches st
    and try_noninvertible active branch history st = function
      | [] -> None
      | rule :: tl ->
          let rec try_results results =
            match results () with
            | Seq.Nil -> try_noninvertible active branch history st tl
            | Seq.Cons (next, rest) -> (
                let fresh_history =
                  List.filter
                    (fun key -> not (List.mem key history))
                    next.Tableau.applied
                in
                let history =
                  if fresh_history = [] then next.applied else fresh_history
                in
                let post_rules =
                  match
                    List.find_opt
                      (fun (rule_id, _, _) -> rule_id = rule.Tableau.id)
                      post_phases
                  with
                  | None -> []
                  | Some (_, rules, _) -> rules
                in
                let next =
                  if post_rules = [] then Some (next.Tableau.tree, history, next)
                  else
                    apply_post_rules post_rules next.Tableau.tree history next
                in
                match next with
                | None -> try_results rest
                | Some (branches, history, next) -> (
                    match solve_children active branches history next with
                    | Some _ as result -> result
                    | None -> try_results rest))
          in
          try_results (run_rule rule branch history st)
    in
    let run_global_rule rule st =
      incr applications;
      rule.Tableau.run st
    in
    let first_global_result rules st =
      let rec loop = function
        | [] -> None
        | rule :: tl -> (
            match Compat.seq_uncons (run_global_rule rule st) with
            | None -> loop tl
            | Some (result, _) -> Some result)
      in
      loop rules
    in
    let rec apply_global_post rules st =
      match first_global_result rules st with
      | None -> st
      | Some next -> apply_global_post rules next
    in
    let rec solve_global active st =
      let tree = canonical_tree st.Tableau.tree in
      if tree = [] then Some { st with Tableau.tree = [] }
      else
        let st = { st with Tableau.tree } in
        let key = key_of_tree tree st.applied st in
        match Cache.find_opt cache key with
        | Some true -> Some { st with Tableau.tree = [] }
        | Some false -> None
        | None when Active.mem key active -> None
        | None -> (
            let active = Active.add key active in
            let finish result =
              Cache.replace cache key (Option.is_some result);
              result
            in
            let rec try_closing = function
              | [] -> None
              | rule :: tl ->
                  let rec try_results results =
                    match results () with
                    | Seq.Nil -> try_closing tl
                    | Seq.Cons (next, rest) -> (
                        match solve_global active next with
                        | Some _ as result -> result
                        | None -> try_results rest)
                  in
                  try_results (run_global_rule rule st)
            in
            match try_closing closing_rules with
            | Some result -> finish (Some result)
            | None -> finish (try_global_invertible active st invertible_rules))
    and try_global_invertible active st = function
      | [] -> try_global_noninvertible active st noninvertible_rules
      | rule :: tl ->
          let rec try_results results =
            match results () with
            | Seq.Nil -> try_global_invertible active st tl
            | Seq.Cons (next, rest) -> (
                match solve_global active next with
                | Some _ as result -> result
                | None -> try_results rest)
          in
          try_results (run_global_rule rule st)
    and try_global_noninvertible active st = function
      | [] -> None
      | rule :: tl ->
          let rec try_results results =
            match results () with
            | Seq.Nil -> try_global_noninvertible active st tl
            | Seq.Cons (next, rest) -> (
                let fresh_history =
                  List.filter
                    (fun key -> not (List.mem key st.Tableau.applied))
                    next.Tableau.applied
                in
                let history =
                  if fresh_history = [] then next.applied else fresh_history
                in
                let post_rules =
                  match
                    List.find_opt
                      (fun (rule_id, _, _) -> rule_id = rule.Tableau.id)
                      post_phases
                  with
                  | None -> []
                  | Some (_, rules, _) -> rules
                in
                let next =
                  { next with Tableau.applied = history }
                  |> apply_global_post post_rules
                in
                match solve_global active next with
                | Some _ as result -> result
                | None -> try_results rest)
          in
          try_results (run_global_rule rule st)
    in
    fun st ->
      Cache.clear cache;
      applications := 0;
      let result =
        if branch_obligations then
          solve_children Active.empty st.Tableau.tree st.applied st
        else solve_global Active.empty st
      in
      match result with
      | None ->
          Log.info "phase applications=%d cache=%d" !applications
            (Cache.length cache);
          Seq.empty
      | Some st' ->
          Log.info "phase applications=%d cache=%d" !applications
            (Cache.length cache);
          Seq.return { st' with Tableau.tree = [] }
  in
  let strategy =
    match (branch_obligations, phase_scheduling) with
    | false, false -> compile_strategy logic.entry_strategy.body
    | true, false -> branch_strategy
    | _, true -> focused_strategy
  in
  (initial_state, strategy)
