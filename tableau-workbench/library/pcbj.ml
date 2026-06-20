
CONNECTIVES [ "~";"&";"v";"->";"<->" ]
GRAMMAR
formula :=
     Atom | Verum | Falsum
    | formula & formula
    | formula v formula
    | formula -> formula
    | formula <-> formula
    | ~ formula
    ;;

expr := int list : formula ;;
END

HISTORIES Idx : int := 0 END
VARIABLES bj  : int list := [] END

(* open Pclib *)
open Twblib
(* open Pcopt *)

TABLEAU

  RULE Id
  { i : a } ; { j : ~ a }
  =======================
          Close

  BACKTRACK [ bj := addlabel(i,j) ]
  END
  
  RULE False _ : Falsum === Close END
  RULE And {l : A & B} === l : A; l : B END
  
  RULE Or 
(*
       { l : A v B } 
  =====================
   Idx :: l : A | Idx :: l : B
*)

       { l : A v B } 
  =====================
   addlabel( l : A ) | addlabel ( l : B )

  ACTION    [[ Idx := inc(Idx) ]; [ Idx := inc(Idx) ]]
  BRANCH    [ backjumping(Idx,bj@1) ]
  BACKTRACK [ bj := mergelabel(bj@all,status@last) ]
  END
  
END

STRATEGY := tactic ( (False|Id|And|Or)* )

PP := List.map nnf
NEG := List.map neg

MAIN
