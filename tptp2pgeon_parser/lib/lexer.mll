{
  open Parser
  exception Lexing_error of string
}

let digit = ['0'-'9']
let lower_alpha = ['a'-'z']
let upper_alpha = ['A'-'Z']
let alpha_num = lower_alpha | upper_alpha | digit | '_'

rule token = parse
| [' ' '\t' '\r'] { token lexbuf }
| '\n'            { Lexing.new_line lexbuf; token lexbuf }

| "fof"           { FOF }
| "qmf"           { QMF }
| "cnf"           { CNF }

| '('             { LPAREN }
| ')'             { RPAREN }
| '['             { LBRACKET }
| ']'             { RBRACKET }
| ','             { COMMA }
| '.'             { DOT }
| ':'             { COLON }
| '~'             { NOT }
| '&'             { AND }
| '|'             { OR }
| "=>"            { IMPLIES }
| "<=>"           { EQUIV }

| '!'             { FORALL }
| '?'             { EXISTS }
| upper_alpha alpha_num* as s { VAR s }

| "[#]"           { BOX }
| "#box"          { BOX }
| "{$box}"        { BOX }
| "<#>"           { DIAMOND }
| "#dia"          { DIAMOND }
| "{$diam}"       { DIAMOND }

| lower_alpha alpha_num* as s { PRED s }
| '%' [^ '\n']*   { token lexbuf }
| eof             { EOF }
| _ as c          { raise (Lexing_error ("Unknown character: " ^ String.make 1 c)) }
