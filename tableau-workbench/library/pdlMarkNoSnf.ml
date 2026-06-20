
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


open PdlMarkNoSnfRewrite
open PdlMarkNoSnfFunctions


HISTORIES
  HCr  : ListFormulaSet.olist := new ListFormulaSet.olist;
  HNx : nextFormula := new nextFormula;
  HBD : FormulaSet.set := new FormulaSet.set;
  HBB : FormulaSet.set := new FormulaSet.set
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
  COND   [ undef_HNx(HNx) ]
  BACKTRACK [ uev := set_uev_All(uev@1, Z) ]
  END

  RULE UnionBox { [ A U B ] P } ; Z === [ A ] P ;  [ B ] P ; Z
  COND   [ undef_HNx(HNx) ]
  BACKTRACK [ uev := set_uev_All(uev@1, Z) ]
  END

  RULE SeqBox { [ A ; B ] P } ; Z === [ A ] [ B ] P ; Z
  COND   [ undef_HNx(HNx) ]
  BACKTRACK [ uev := set_uev_All(uev@1, Z) ]
  END

  RULE StarBox1 { [ * A ] P } ; Z === P ; [ A ] [ * A ] P ; Z 
  COND   [ undef_HNx(HNx) ; notinHB([ * A ] P, HBB) ]
  ACTION [ [ HBB := pushHBB([ * A ] P, HBB) ] ]
  BACKTRACK [ uev := set_uev_All(uev@1, Z) ]
  END

  RULE StarBox2 { [ * A ] P } ; Z === Z 
  COND   [ undef_HNx(HNx) ; inHB([ * A ] P, HBB) ]
  BACKTRACK [ uev := set_uev_All(uev@1, Z) ]
  END

  RULE TestDia { < ? F > P } ; Z === F ; P ; Z
  COND   [ undefOrP_HNx(HNx, < ? F > P) ]
  ACTION [ [ HNx := testchain_HNx(P);
             HBD := testchain_HBD(P, HBD) ] ]
  BACKTRACK [ uev := set_uev_Inh(uev@1, < ? F > P, P, Z) ]
  END

  RULE SeqDia { < A ; B > P } ; Z === < A > < B > P ; Z
  COND   [ undefOrP_HNx(HNx, < A ; B > P) ]
  ACTION [ [ HNx := testchain_HNx(< A > < B > P);
             HBD := testchain_HBD(< A > < B > P, HBD) ] ]
  BACKTRACK [ uev := set_uev_Inh(uev@1, < A ; B > P, < A > < B > P, Z) ]
  END

  RULE Or
        { P v Q } ; Z 
  ====================
      P ; Z ||| Q ; Z

  COND   [ undef_HNx(HNx) ]
  BRANCH [ [ doNextChild_disj(mrk@1, uev@1) ] ]
  BACKTRACK [
      uev := uev_disj_all(mrk@all, uev@all, Z);
      mrk := mrk_disj(mrk@all)
  ]
  END

  RULE TestBox
  { [ ? F ] P } ; Z === nnf ( ~ F ) ; Z ||| P ; Z

  COND   [ undef_HNx(HNx) ]
  BRANCH [ [ doNextChild_disj(mrk@1, uev@1) ] ]
  BACKTRACK [
      uev := uev_disj_all(mrk@all, uev@all, Z);
      mrk := mrk_disj(mrk@all)
  ]
  END

  RULE UnionDia
  { < A U B > P } ; Z === < A > P ; Z ||| < B > P ; Z

  COND   [ undefOrP_HNx(HNx, < A U B > P) ]
  ACTION [ [ HNx := testchain_HNx(< A > P);
             HBD := testchain_HBD(< A > P, HBD) ];
           [ HNx := testchain_HNx(< B > P);
             HBD := testchain_HBD(< B > P, HBD) ] ]
  BRANCH [ [ doNextChild_disj(mrk@1, uev@1) ] ]
  BACKTRACK [
      uev := uev_disj_union(mrk@all, uev@all, < A U B > P, < A > P, < B > P, Z);
      mrk := mrk_disj(mrk@all)
  ]
  END

  RULE StarDia1
  { < * A > P } ; Z === P ; Z ||| < A > < * A > P ; Z 

  COND   [ undefOrP_HNx(HNx, < * A > P) ; notinHB(< * A > P, HBD) ]
  ACTION [ [ HNx := testchain_HNx(P);
             HBD := testchain_HBD_Star(P, HBD, < * A > P) ];
           [ HNx := testchain_HNx(< A > < * A > P);
             HBD := testchain_HBD_Star(< A > < * A > P, HBD, < * A > P) ] ]
  BRANCH [ [ doNextChild_disj(mrk@1, uev@1) ] ]
  BACKTRACK [
      uev := uev_disj_star(mrk@all, uev@all, < * A > P , P, < A > < * A > P, Z);
      mrk := mrk_disj(mrk@all)
  ]
  END

  RULE StarDia2
  { < * A > P } ; Z === Stop

  COND   [ undefOrP_HNx(HNx, < * A > P) ; inHB(< * A > P, HBD) ]
  BACKTRACK [
      uev := uevundef ();
      mrk := true
  ]
  END

  RULE K 
  { < A > P } ; [ A ] Y ; < B > E ; [ C ] F ; Z
  ==============================================
      P ; Y ||| [ A ] Y ; < B > E ; [ C ] F

  COND   [ loop_check(P, Y, HCr) ]
  ACTION [ [ HCr := push(P, Y, HCr);
             HNx := testchain_HNx(P);
             HBB := emptySet();
             HBD := emptySet() ]; [] ]
  BRANCH [ [ test_ext(mrk@1, uev@1, P, HCr) ] ]
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
      uev := uev_loop(< A > X, [ B ] Y, HCr);
      mrk := false
  ]
  CACHE := true
  END

END

STRATEGY := 
    let sat = tactic ( (  False ! Id ! StarDia2
                        ! And ! StarBox1 ! StarBox2 !UnionBox ! SeqDia ! SeqBox ! TestDia
                        ! Or ! StarDia1 ! UnionDia ! TestBox) )
    in tactic ( (sat ! K ! Loop)* )

let exit = function
  | true -> "Closed"
  | false -> "Open"

PP := List.map nnf_term
NEG := List.map neg_term
EXIT := exit (mrk@1)

MAIN
