
CONNECTIVES
[ "~";"&";"v";"->";"<->";"<";">";"[";"]";"U";"*";";";"?"]

GRAMMAR
program := 
      * program
    | ? formula
    | program U program
    | program ; program
    | ATOM
;;

formula :=
     ATOM | Verum | Falsum
    | formula & formula
    | formula v formula
    | formula -> formula
    | formula <-> formula
    | < program > formula 
    | [ program ] formula 
    | ~ formula
;;

expr := formula;;
END


open PdlMarkRewrite
open PdlMarkFunctions


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

  RULE And { A & B } ; Z === A ; B ; Z 
  BACKTRACK [ uev := set_uev_All(uev@1, Z) ]
  END

  RULE UnionBox { [ A U B ] P } ; Z === [ A ] P ;  [ B ] P ; Z
  BACKTRACK [ uev := set_uev_All(uev@1, Z) ]
  END

  RULE SeqBox { [ A ; B ] P } ; Z === [ A ] [ B ] P ; Z
  BACKTRACK [ uev := set_uev_All(uev@1, Z) ]
  END

  RULE StarBox { [ * A ] P } ; Z === P ; [ A ] [ * A ] P ; Z 
  BACKTRACK [ uev := set_uev_All(uev@1, Z) ]
  END

  RULE TestDia { < ? F > P } ; Z === F ; P ; Z
  BACKTRACK [ uev := set_uev_Inh(uev@1, < ? F > P, P, Z) ]
  END

  RULE SeqDia { < A ; B > P } ; Z === < A > < B > P ; Z
  BACKTRACK [ uev := set_uev_Inh(uev@1, < A ; B > P, < A > < B > P, Z) ]
  END

  RULE Or
        { P v Q } ; Z 
  ====================
      P ; Z ||| Q ; Z

  BRANCH [ [ doNextChild_disj(mrk@1, uev@1) ] ]
  BACKTRACK [
      uev := uev_disj_all(mrk@all, uev@all, Z);
      mrk := mrk_disj(mrk@all)
  ]
  END

  RULE TestBox
  { [ ? F ] P } ; Z === nnf ( ~ F ) ; Z ||| P ; Z

  BRANCH [ [ doNextChild_disj(mrk@1, uev@1) ] ]
  BACKTRACK [
      uev := uev_disj_all(mrk@all, uev@all, Z);
      mrk := mrk_disj(mrk@all)
  ]
  END

  RULE UnionDia
  { < A U B > P } ; Z === < A > P ; Z ||| < B > P ; Z

  BRANCH [ [ doNextChild_disj(mrk@1, uev@1) ] ]
  BACKTRACK [
      uev := uev_disj_union(mrk@all, uev@all, < A U B > P, < A > P, < B > P, Z);
      mrk := mrk_disj(mrk@all)
  ]
  END

  RULE StarDia
  { < * A > P } ; Z === P ; Z ||| < A > < * A > P ; Z 

  BRANCH [ [ doNextChild_disj(mrk@1, uev@1) ] ]
  BACKTRACK [
      uev := uev_disj_star(mrk@all, uev@all, < * A > P , P, < A > < * A > P, Z);
      mrk := mrk_disj(mrk@all)
  ]
  END

  RULE K 
  { < A > P } ; [ A ] Y ; < B > E ; [ C ] F ; Z
  ==============================================
       P ; Y ||| [ A ] Y ; < B > E ; [ C ] F

  COND   [ loop_check(P, Y, HCore) ]
  ACTION [ [ HCore := push(P, Y, HCore) ] ; [] ]
  BRANCH [ [ test_ext(mrk@1, uev@1, P, HCore) ] ]
  BACKTRACK [
      uev := uev_ext(mrk@all, uev@all, < A > P, P);
      mrk := mrk_ext(mrk@all)
  ]
  CACHE := true
  END

  RULE Loop
       < A > X ; [ B ] Y
       ==================
             Stop

  BACKTRACK [
      uev := uev_loop(< A > X, [ B ] Y, HCore);
      mrk := false
  ]
  CACHE := true
  END

END

STRATEGY := 
    let sat = tactic ( (  False ! Id
                        ! And ! StarBox ! UnionBox ! SeqDia ! SeqBox ! TestDia
                        ! Or ! StarDia ! UnionDia ! TestBox) )
    in tactic ( (sat ! K ! Loop)* )

let exit = function
  | true -> "Closed"
  | false -> "Open"

PP := List.map nnf_snf_term
NEG := List.map neg_term
EXIT := exit (mrk@1)

MAIN
