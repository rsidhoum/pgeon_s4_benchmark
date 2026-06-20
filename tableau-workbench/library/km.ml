
CONNECTIVES [ "~";"&";"v";"->";"<->";"[";"]";"<";">" ]
GRAMMAR
idx := One | Two ;;
formula :=
     ATOM | Verum | Falsum
    | idx
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
  { < I > A } ; [ I ] X ; < I > Y ; Z
  ===========================
      A ; X || < I > Y ; [ I ] X

  BRANCH [ not_emptylist(< I > Y) ]
  END 
   
  RULE K
  { < I > A } ; [ I ] X ;  Z
  ----------------------
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

