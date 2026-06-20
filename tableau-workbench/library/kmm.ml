
CONNECTIVES [ "~";"&";"v";"->";"<->";"[";"]";"<>";"<";">" ]
GRAMMAR
idx := One | Two ;;
formula :=
     ATOM | Verum | Falsum
    | formula & formula
    | formula v formula
    | formula -> formula
    | formula <-> formula
    | [ idx ] formula
    | < idx > formula
    | ~ formula
;;

expr := formula ;;
END

open Twblib
open Kmlib

TABLEAU

  RULE K1
  { < One > A } ; [ One ] X ;  Z
  ------------------------------
             A ; X
  END 

  RULE K2
  { < Two > A } ; [ Two ] X ;  Z
  ------------------------------
             A ; X
  END 

  RULE Id { a } ; { ~ a } === Close END
  RULE False Falsum === Close END
  RULE And { A & B } === A ; B END
  RULE Or { A v B } === A | B END
  
END

STRATEGY := 
    let sat = tactic ( (Id ! False ! And ! Or) ) in
    tactic ( ((sat)* ; (K1 || K2)  )* )

PP := List.map nnf
NEG := List.map neg

MAIN

