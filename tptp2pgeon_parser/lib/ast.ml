type expr =
  | EVar of string
  | EApp of string * expr list
  | EBind of string * string * expr
  | EModal of string * expr

type formula_role = Axiom | Conjecture

type problem_decl = {
  formulas : (formula_role * expr) list;
}