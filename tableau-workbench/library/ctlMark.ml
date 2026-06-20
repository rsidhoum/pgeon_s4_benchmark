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

open CtlMarkFunctions
open CtlMarkRewrite

HISTORIES
  HCore  : ListFormulaSet.olist := new ListFormulaSet.olist
END

VARIABLES
  uev : FormulaIntSet.set := new FormulaIntSet.set;
  mrk : bool := false
END

let nnf = List.map nnf_term 

TABLEAU

  RULE Id { P } ; { ~ P } == Stop 
  BACKTRACK [ 
      uev := uevundef ();
      mrk := true 
  ]
  END

  RULE False { Falsum } == Stop 
  BACKTRACK [ 
      uev := uevundef ();
      mrk := true 
  ]
  END

  RULE And P & Q == P ; Q END
  RULE Exb { E P B Q } == nnf(~ Q) ; P v EX (E P B Q) END
  RULE Axb { A P B Q } == nnf(~ Q) ; P v AX (A P B Q) END

  RULE Or
  { P v Q }
  =========
   P ||| Q

  BRANCH [ [ doNextChild_disj(mrk@1, uev@1, P v Q) ] ] 
  BACKTRACK [ 
      uev := uev_disj(mrk@all, uev@all, P v Q);
      mrk := mrk_disj(mrk@all)
  ]
  END

  RULE Exu
      { E P U Q }
  ===================
  Q ||| P ; EX (E P U Q)

  BRANCH [ [ doNextChild_disj(mrk@1, uev@1, E P U Q) ] ] 
  BACKTRACK [ 
      uev := uev_disj(mrk@all, uev@all, E P U Q);
      mrk := mrk_disj(mrk@all)
  ]
  END 

  RULE Axu
      { A P U Q }
  ===================
  Q ||| P ; AX (A P U Q)

  BRANCH    [ doNextChild_disj(mrk@1, uev@1, A P U Q) ]
  BACKTRACK [ 
      uev := uev_disj(mrk@all, uev@all, A P U Q);
      mrk := mrk_disj(mrk@all)
  ]
  END 

  RULE D
  EX Y ;  AX Z ; P == EX Verum ; AX Z ; P
  COND [ condD(EX Y, AX Z) ]
  END

  RULE Exx
         { EX P } ; EX X ; AX Y ; Z 
  ===========================================
    P ; Y ||| EX X ; emptycheck(EX X, AX Y)

  COND   [ loop_check(P, Y, HCore) ]
  ACTION [ [ HCore := push(P, Y, HCore) ] ; [] ] 
  BRANCH [ [ test_ext(mrk@1, uev@1, P, Y, HCore) ] ]
  BACKTRACK [
      uev := uev_ext(mrk@all, uev@all, P, Y);
      mrk := mrk_ext(mrk@all)
  ]
  CACHE := true
  END

  RULE Loop
        EX X ; AX Y  
  ==========================
           Stop

  BACKTRACK [
      uev := uev_loop(X, Y, HCore);
      mrk := false
  ]
  CACHE := true
  END

END

let exit = function
  | true -> "Closed"
  | false -> "Open"
 
PP := List.map nnf_term
NEG := List.map neg_term
EXIT := exit (mrk@1)
  
let saturation = tactic ( (Id ! False ! And ! Exb ! Axb ! Or ! Axu ! Exu ) )
let modal = tactic ( (saturation ! D ! Exx ! Loop ) )
STRATEGY := tactic ( (modal)* )

MAIN
