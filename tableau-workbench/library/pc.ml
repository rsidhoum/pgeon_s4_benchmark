
CONNECTIVES [ "~";"&";"v";"->";"<->" ]
GRAMMAR
formula :=
     ATOM | Verum | Falsum
    | formula & formula
    | formula v formula
    | formula -> formula
    | formula <-> formula
    | ~ formula 
    ;;

expr := formula ;;
END

open Pclib

TABLEAU

  RULE Id { a } ; { ~ a } === Close END
  RULE False Falsum === Close END
  RULE And { A & B } === A ; B END
  RULE Or { A v B } === A | B END

END

STRATEGY := tactic ( (False ! Id ! And ! Or)* )

PP := List.map nnf
NEG := List.map neg

MAIN

