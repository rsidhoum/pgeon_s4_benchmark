
CONNECTIVES [
    "~";"&";"v";"->";"<->";
    "E";"A";"U";"B";
    "AG";"EF";
    "EG";"AF";
    "AX";"EX"
]
GRAMMAR
formula :=
     ATOM | Verum | Falsum
    | formula & formula
    | formula v formula
    | formula -> formula
    | formula <-> formula
    | E formula B formula
    | E formula U formula
    | A formula B formula
    | A formula U formula
    | AF formula
    | EF formula
    | AG formula
    | EG formula
    | EX formula
    | AX formula
    | ~ formula
;;

expr := formula ;;
END

open Twblib
open CtlFunctions
open CtlRewrite

HISTORIES
  Fev : FormulaSet.set := new FormulaSet.set;
  Br  : ListFormulaSet.olist := new ListFormulaSet.olist
END

VARIABLES
  uev : FormulaIntSet.set := new FormulaIntSet.set;
  fev : FormulaIntSet.set := new FormulaIntSet.set;
  status : string := "Undef" 
END

let nnf = List.map nnf_term 

TABLEAU

  RULE Id
  { P } ; { ~ P } == Stop
  BACKTRACK [ uev := setclose (Br) ]
  END
  
  RULE False
  { Falsum } == Stop
  BACKTRACK [ uev := setclose (Br) ]
  END

  RULE Exu
      { E P U Q }
  ===================
  Q ||| P ; EX (E P U Q)

  ACTION [ [ Fev := add(E P U Q, Fev) ] ; [] ]
  BRANCH [ [ not_emptyset(uev@1) ] ] 
  BACKTRACK [ uev := setuev_beta(uev@1, uev@2, Br) ] 
  END 

  RULE Axu
      { A P U Q }
  ===================
  Q ||| P ; AX (A P U Q)

  ACTION [ [ Fev := add(A P U Q, Fev) ] ; [] ]
  BRANCH [ [ not_emptyset(uev@1) ] ] 
  BACKTRACK [ uev := setuev_beta(uev@1, uev@2, Br) ] 
  END 

  RULE Exx
  { EX P } ; EX S ; AX Y ; Z
  =============================
      P ; Y ||| EX S ; AX Y
      
  COND [ loop_check(P, Y, Br) ]
  ACTION [ [
      Br  := push(P, Y, Fev, Br); 
      Fev := emptyset(Fev)
  ] ; [] ] 
  BRANCH [ [ not_false(uev@1) ; not_emptylist(EX S) ] ]
  BACKTRACK [ uev := setuev_pi(uev@1, uev@2, Br) ]
  CACHE := true
  END

  RULE D
  EX Y ;  (AX P) == EX Verum ; AX P
  COND [ is_emptylist(EX Y) ]
  END

  RULE Loop
  EX P ; AX Y == Stop
  COND [ not_emptylist(EX P) ]
  BACKTRACK [ uev := setuev_loop(P, Y, Fev, Br) ]
  END

  RULE Or
  { P v Q }
  =========
   P ||| Q

  BRANCH [ [ not_emptyset(uev@1) ] ] 
  BACKTRACK [ uev := setuev_beta(uev@1, uev@2, Br) ] 
  END

  RULE And P & Q == P ; Q END
  RULE Exb { E P B Q } == nnf(~ Q) ; P v EX (E P B Q) END
  RULE Axb { A P B Q } == nnf(~ Q) ; P v AX (A P B Q) END

END

let exit (uev) =
    match uev#elements with
    |(termfalse,_)::[] -> "Closed"
    |[] -> "Open"
    |_ -> "Closed"
;;

(*
OPTIONS 
    ("-D", (Arg.Set debug), "Enable debug")
END
*)
 
let exit (uev) = match uev#elements with
    |[] -> "Open"
    |[formula ( Falsum ),_] -> "Closed"
    |_ -> "Closed"
 
PP := List.map nnf_term
NEG := List.map neg_term
EXIT := exit (uev@1)
  
let saturation = tactic ( (Id ! False ! And ! Or ! Axu ! Exu ! Exb ! Axb ) )
let modal = tactic ( (saturation ! D ! Exx ! Loop) )
STRATEGY := tactic ( (modal)* )

MAIN
