
CONNECTIVES [ "~";"&";"v";"->";"<->";"Un";"Bf";"X";"G";"F" ]
GRAMMAR
formula :=
     ATOM | Verum | Falsum
    | formula & formula
    | formula v formula
    | formula -> formula
    | formula <-> formula
    | formula Un formula
    | formula Bf formula
    | F formula
    | G formula
    | X formula
    | ~ formula
;;

expr := formula ;;
END

open Twblib
open PltlRewrite
open PltlFunctions


HISTORIES
  Ev : FormulaSet.set := new FormulaSet.set;
  Br : ListFormulaSet.olist := new ListFormulaSet.olist
END

VARIABLES
  uev : FormulaSet.set := new FormulaSet.set;
  status : string := "Undef";
  n : int := 0
END

let neg = List.map neg_term ;;
let nnf = List.map nnf_term ;;

TABLEAU

  RULE Id
  { A } ; { ~ A } 
  ===============
     Stop

  BACKTRACK [
      uev := setclose();
      n := setclosen (Br)
  ]

  END
  
  RULE False
     { Falsum }
  ===============
     Stop

  BACKTRACK [
      uev := setclose();
      n := setclosen (Br)
  ]

  END

  RULE Loop
  { X A } ; X B ; Z
  =================
       Stop

  BACKTRACK [
      uev := setuev(X A, X B, Z, Ev, Br);
      n   := setn (X A, X B, Z, Br)
  ]

  END

  RULE Next
  { X A } ; X B ; Z
  =================
      A ; B
      
  COND [ loop_check(X A, X B, Z, Br) ]
  ACTION [
      Ev := emptyset(Ev);
      Br := push(X A, X B, Z, Ev, Br)
  ]

  END

  RULE Before
           {A Bf C}
  ==========================
   nnf (~ C) ; A v X (A Bf C) 

  END

  RULE Until
           { C Un D } 
  =============================
      D ||| C ; X ( C Un D ) 

  ACTION    [ Ev := add(D, Ev) ] 
  BRANCH    [ not_emptyset(uev@1) ] 
  BACKTRACK [ 
      uev := beta(uev@1, uev@2, n@1, n@2, Br);
      n := min (n@1, n@2)
  ]
    
  END
 
  RULE Or
  { A v B }
  =========
   A ||| B

  BRANCH [ not_emptyset(uev@1) ]  
  BACKTRACK [ 
      uev := beta(uev@1, uev@2, n@1, n@2, Br);
      n := min (n@1 , n@2)
  ]

  END

  RULE And
    A & B 
  =========
    A ; B
  END

  RULE Ge
     { G A }
  =============
   A ; X (G A)
  END
  
END


let exit (uev) = match uev#elements with
    |[] -> "Open"
    |[formula ( Falsum )] -> "Closed"
    |_ -> "Closed"
(*
OPTIONS
    ("-D", (Arg.Set debug), "Enable debug")
END
*)
 
PP := nnf
NEG := neg
EXIT := exit (uev@1)

let sat = tactic ( (Id ! False ! And ! Before ! Ge ! Or ! Until) )

STRATEGY := tactic ((sat ! Next ! Loop)* )

MAIN
