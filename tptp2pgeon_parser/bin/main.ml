open Tptp_parser
open Ast

type target_prover = Pgeon | Twb

let target = ref Pgeon
let anon_files = ref []

let print_error_position lexbuf =
  let pos = lexbuf.Lexing.lex_curr_p in
  Printf.eprintf "Syntax error: line %d, column %d (character %d)\n"
    pos.pos_lnum
    (pos.pos_cnum - pos.pos_bol + 1)
    pos.pos_cnum

let has_conjecture ast =
  List.exists (fun (role, _) -> role = Ast.Conjecture) ast.formulas

let refutation_ast ast =
  {
    formulas =
      List.map
        (fun (role, f) ->
          match role with
          | Ast.Axiom -> (Ast.Axiom, f)
          | Ast.Conjecture -> (Ast.Conjecture, EApp ("not", [ f ])))
        ast.formulas;
  }

let should_negate_conjecture = function
  | Status.Theorem -> true
  | Status.Unsatisfiable
  | Status.NonTheorem
  | Status.Satisfiable
  | Status.Unsolved
  | Status.UnknownStatus -> false

let speclist = [
  ("--pgeon", Arg.Unit (fun () -> target := Pgeon), " Translate TPTP to Pgeon syntax (default)");
  ("--twb",   Arg.Unit (fun () -> target := Twb),   " Translate TPTP to TWB syntax");
]

let usage_msg = "Usage: " ^ Sys.argv.(0) ^ " [--pgeon | --twb] <file.p>"

let () =
  Arg.parse speclist (fun anonymous_arg -> anon_files := anonymous_arg :: !anon_files) usage_msg;

  match !anon_files with
  | [] ->
      Arg.usage speclist usage_msg;
      exit 1
  | _ :: _ :: _ ->
      Printf.eprintf "Error: Only one file can be processed at a time.\n";
      exit 1
  | [filename] ->
      let status = Status.extract_status filename in

      let status_str = Status.to_string status in

      let ic = open_in filename in
      let lexbuf = Lexing.from_channel ic in
      lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };

      try
        let ast = Parser.problem Lexer.token lexbuf in
        close_in ic;

        let final_ast =
          if has_conjecture ast && should_negate_conjecture status then
            refutation_ast ast
          else ast
        in
        begin
          match !target with
          | Pgeon -> Writer.print_problem final_ast status_str
          | Twb -> Twb_writer.print_problem final_ast status_str
        end

      with
      | Parser.Error -> close_in_noerr ic; print_error_position lexbuf; exit 1
      | Lexer.Lexing_error _msg -> close_in_noerr ic; print_error_position lexbuf; exit 1
      | e -> close_in_noerr ic; Printf.eprintf "Unexpected error: %s\n" (Printexc.to_string e); exit 1
