open Ast

module StringSet = Set.Make(String)
module Signature = Set.Make(struct
  type t = string * int
  let compare = compare
end)

let rec expr_to_pgeon = function
  | EApp ("and", [a; b]) ->
    Printf.sprintf "and(%s, %s)" (expr_to_pgeon a) (expr_to_pgeon b)
  | EApp ("not", [f]) ->
      Printf.sprintf "not(%s)" (expr_to_pgeon f)
  | EApp ("or", [a; b]) ->
      Printf.sprintf "or(%s, %s)" (expr_to_pgeon a) (expr_to_pgeon b)
  | EApp ("implies", [a; b]) ->
      Printf.sprintf "imp(%s, %s)" (expr_to_pgeon a) (expr_to_pgeon b)
  | EApp ("equ", [a; b]) ->
    Printf.sprintf "equ(%s, %s)" (expr_to_pgeon a) (expr_to_pgeon b)
  | EVar v -> v
  | EBind (binder, var, body) ->
      Printf.sprintf "%s %s. %s" binder var (expr_to_pgeon body)
  | EModal (kind, body) ->
      Printf.sprintf "%s(%s)" kind (expr_to_pgeon body)
  | EApp (name, []) -> name ^ "()"
  | EApp (name, args) ->
      let translated_args = List.map expr_to_pgeon args in
      Printf.sprintf "%s(%s)" name (String.concat ", " translated_args)
;;

let rec collect_signatures acc = function
  | EApp (name, args) ->
      let builtins = ["and"; "or"; "not"; "imp"; "implies"; "equ"] in
      let acc =
        if List.mem name builtins then acc
        else Signature.add (name, List.length args) acc
      in
      List.fold_left collect_signatures acc args
  | EBind (_, _, body) -> collect_signatures acc body
  | EModal (_, body) -> collect_signatures acc body
  | EVar _ -> acc
;;

let generate_header (prob : problem_decl) =
  let pure_formulas = List.map snd prob.formulas in
  let all_sigs = List.fold_left collect_signatures Signature.empty pure_formulas in
  if Signature.is_empty all_sigs then ""
  else
    let names = Signature.elements all_sigs
                |> List.map fst
                |> String.concat " " in
    Printf.sprintf "function %s: -> formula\n\n" names
;;

let rec get_free_vars bound acc = function
  | EVar v ->
      if StringSet.mem v bound then acc else StringSet.add v acc
  | EApp (_, args) ->
      List.fold_left (get_free_vars bound) acc args
  | EModal (_, body) ->
      get_free_vars bound acc body
  | EBind (_, var, body) -> get_free_vars (StringSet.add var bound) acc body
;;

let close_formula expr =
  let free_vars = get_free_vars StringSet.empty StringSet.empty expr in
  StringSet.fold (fun var acc_expr ->
    EBind ("forall", var, acc_expr)
  ) free_vars expr
;;

let print_problem (prob : problem_decl) (expected_status : string) =
  print_string (generate_header prob);
  Printf.printf "/* expected: %s */\n" expected_status;
  List.iter (fun (_, f) ->
    let closed_f = close_formula f in
    let s = expr_to_pgeon closed_f in
    Printf.printf "%s ;\n" s
  ) prob.formulas
;;
