
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

expr := int list : formula ;;
END

module ListInt = TwbList.Make(
    struct
        type t = int
        let to_string s = Printf.sprintf "%d" s
        let copy s = s
    end
)


HISTORIES
  Idx    : int := 0
END

VARIABLES
  bj     : ListInt.olist := new ListInt.olist
END

open Twblib
open Klib
open Pcopt

TABLEAU

  RULE K
  { <> a } ; [] x ; z
  ----------------------
    a ; x

  BACKTRACK [ bj := mergelabel(bj@all, status@last) ]
  END (cache)

  RULE Id
  { a } ; { ~ a }
  ===============
    Close

  BACKTRACK [ bj := addlabel(a, ~ a) ]
  END

  RULE False
    Falsum
  =========
    Close
  END

  RULE And
  { a & b }
  ==========
    a ; b
  END
  
  RULE Or
  { a v b } 
 =================================
     fixlabel(Idx,a) | fixlabel(Idx,b) ; nnf_term(~ a)
   
  ACTION    [[ Idx := inc(Idx) ]; [ Idx := inc(Idx) ]]
  BRANCH    [ backjumping(Idx, bj@1) ]
  BACKTRACK [ bj := mergelabel(bj@all, status@last) ]

  END

END

PP := Kopt.nnf
NEG := neg

let saturate = tactic ( False!Id!And!Or )
STRATEGY := ( ( saturate ! K )* )

