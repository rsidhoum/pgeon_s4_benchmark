open Ast

let rec expr_to_twb = function
  | EApp ("and", [a; b]) ->
      Printf.sprintf "(%s & %s)" (expr_to_twb a) (expr_to_twb b)
  | EApp ("not", [f]) ->
      Printf.sprintf "(~ %s)" (expr_to_twb f)
  | EApp ("or", [a; b]) ->
      Printf.sprintf "(%s v %s)" (expr_to_twb a) (expr_to_twb b)
  | EApp ("implies", [a; b]) ->
      Printf.sprintf "(%s -> %s)" (expr_to_twb a) (expr_to_twb b)
  | EApp ("equ", [a; b]) ->
      Printf.sprintf "(%s <-> %s)" (expr_to_twb a) (expr_to_twb b)
  | EVar v -> v
  | EModal ("box", body) ->
      Printf.sprintf "([] %s)" (expr_to_twb body)
  | EModal ("diam", body) ->
      Printf.sprintf "(<> %s)" (expr_to_twb body)
  | EModal (other_kind, body) ->
      let sym = if other_kind = "box" then "[]" else "<>" in
      Printf.sprintf "(%s %s)" sym (expr_to_twb body)
  | EApp (name, []) -> name
  | EApp (name, args) ->
      let translated_args = List.map expr_to_twb args in
      Printf.sprintf "%s(%s)" name (String.concat ", " translated_args)
  | EBind (binder, var, body) ->
      Printf.sprintf "(%s %s. %s)" binder var (expr_to_twb body)

      let print_problem (prob : problem_decl) (_expected_status : string) =
        (* Printf.printf "/* expected: %s */\n" expected_status; *)

        match prob.formulas with
        | [] -> ()
        | [(_, seule_formule)] ->
            let s = expr_to_twb seule_formule in
            Printf.printf "%s\n" s
        | premiere_paire :: reste_paires ->
            let premiere = snd premiere_paire in
            let reste = List.map snd reste_paires in
            let grosse_conjonction =
              List.fold_left (fun acc_expr f -> EApp ("and", [acc_expr; f])) premiere reste
            in
            let s = expr_to_twb grosse_conjonction in
            Printf.printf "%s\n" s
      ;;
