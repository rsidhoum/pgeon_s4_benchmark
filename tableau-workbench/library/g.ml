(*
 This is just a version of K4 but with the transitional rule changed
 to handle the Goedel-Loeb logic KG.
*)

source K

open Twblib
open Klib

TABLEAU

  RULE False Falsum           == Close  END
  RULE Id    { A } ; { ~ A }  == Close  END   (* not just atoms!       *)
  RULE And    X & Y           == X ; Y  END   (* Rewriting all at once *)
  RULE Or    { A v B }        == A | B  END

  RULE K4G
  { <> A } ; [] X ; Z
  ---------------------------------------
  A ; ~ (<> A) ; [] (~ (<> A)) ; X ; [] X
  END

END

PP := nnf
NEG := neg

let sat = tactic (False|Id|And|Or)

STRATEGY tactic ( ( sat ! K4G )* )

