%{
  open Ast
%}

%token FOF QMF CNF
%token LPAREN RPAREN LBRACKET RBRACKET
%token COMMA DOT COLON
%token NOT AND OR IMPLIES EQUIV
%token FORALL EXISTS
%token BOX DIAMOND
%token <string> PRED
%token <string> VAR
%token EOF

%left EQUIV
%right IMPLIES
%left OR
%left AND
%nonassoc NOT BOX DIAMOND


%start <Ast.problem_decl> problem
%%


term:
| v = VAR                                                           { EVar v }
| id = PRED                                                        { EApp (id, []) }
(* | id = PRED; LPAREN; args = separated_list(COMMA, term); RPAREN    { EApp (id, args) } *) (* FONCTIONS ? *)

formula:
| id = PRED; LPAREN; args = separated_list(COMMA, term); RPAREN    { EApp (id, args) }
| id = PRED { EApp (id, []) }
| LPAREN; f = formula; RPAREN                                       { f }
| BOX; COLON; f = formula                                           { EModal ("box", f) }
| DIAMOND; COLON; f = formula                                       { EModal ("diam", f) }
| NOT; f = formula                                                  { EApp ("not", [f]) }
| FORALL; LBRACKET; v = VAR; RBRACKET; COLON; f = formula           { EBind ("forall", v, f) }
| EXISTS; LBRACKET; v = VAR; RBRACKET; COLON; f = formula           { EBind ("exists", v, f) }
| f1 = formula; AND; f2 = formula                                   { EApp ("and", [f1; f2]) }
| f1 = formula; OR; f2 = formula                                    { EApp ("or", [f1; f2]) }
| f1 = formula; IMPLIES; f2 = formula                               { EApp ("implies", [f1; f2]) }
| f1 = formula; EQUIV; f2 = formula                                 { EApp ("equ", [f1; f2]) }

declaration:
| QMF; LPAREN; _name = PRED; COMMA; role = PRED; COMMA; f = formula; RPAREN; DOT
    { let r = if role = "conjecture" then Ast.Conjecture else Ast.Axiom in (r, f) }
| FOF; LPAREN; _name = PRED; COMMA; role = PRED; COMMA; f = formula; RPAREN; DOT
    { let r = if role = "conjecture" then Ast.Conjecture else Ast.Axiom in (r, f) }
| CNF; LPAREN; _name = PRED; COMMA; role = PRED; COMMA; f = formula; RPAREN; DOT
    { let r = if role = "conjecture" then Ast.Conjecture else Ast.Axiom in (r, f) }

problem:
| ds = list(declaration); EOF
    { { formulas = ds } }
