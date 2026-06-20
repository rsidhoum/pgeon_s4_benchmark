val compile :
  ?focused:bool ->
  ?branch_obligations:bool ->
  ?phase_scheduling:bool ->
  Registry.t ->
  Ast.logic_decl ->
  Ast.problem_decl ->
  Tableau.proof_state * Tableau.strategy
(** Compile parsed declarations into an initial proof state and executable
    strategy. *)
