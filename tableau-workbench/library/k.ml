
CONNECTIVES [ "~";"&";"v";"->";"<->";"<>";"[]" ]
GRAMMAR

formula :=
     ATOM | Verum | Falsum
    | formula & formula
    | formula v formula
    | formula -> formula
    | formula <-> formula
    | [] formula
    | <> formula
    | ~ formula
;;

expr := formula ;;
END

open Twblib
open Klib

TABLEAU

  RULE K1
  { <> A } ; [] X ; <> Y ; Z
  ===========================
      A ; X || <> Y ; [] X

  BRANCH [ not_emptylist(<> Y) ]
  END 
   
  RULE K
  { <> A } ; [] X ;  Z
  --------------------
          A ; X
  END 

  RULE Id { a } ; { ~ a } === Close END
  RULE False Falsum === Close END
  RULE And { A & B } === A ; B END
  RULE Or { A v B } === A | B END
  
END


STRATEGY := 
    let sat = tactic ( (Id ! False ! And ! Or) ) in
    tactic ( ((sat)* ; K )* )

PP := List.map nnf
NEG := List.map neg

MAIN

