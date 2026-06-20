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


open PdlMarkNoUevRewrite
open PdlMarkNoUevFunctions


HISTORIES
  HCr  : ListFormulaSet.olist := new ListFormulaSet.olist;
  HNx : nextFormula := new nextFormula;
  HBD : FormulaSet.set := new FormulaSet.set;
  HBB : FormulaSet.set := new FormulaSet.set;
  Hfoc : nextFormula := new nextFormula;
  Hchn : FormulaIntSet.set := new FormulaIntSet.set;
  Dpt : depth := new depth
END

VARIABLES
  mrk : bool := false
END

let nnf = List.map nnf_term

TABLEAU
  RULE Id { P } ; { ~ P } == Stop
  BACKTRACK [ mrk := true ]
  END

  RULE False { Falsum } == Stop
  BACKTRACK [ mrk := true ]
  END

  RULE And { A & B } ; Z === A ; B ; Z 
  COND   [ undef_HNx(HNx) ]
  END

  RULE UnionBox { [ A U B ] P } ; Z === [ A ] P ;  [ B ] P ; Z
  COND   [ undef_HNx(HNx) ]
  END

  RULE SeqBox { [ A ; B ] P } ; Z === [ A ] [ B ] P ; Z
  COND   [ undef_HNx(HNx) ]
  END

  RULE StarBox1 { [ * A ] P } ; Z === P ; [ A ] [ * A ] P ; Z 
  COND   [ undef_HNx(HNx) ; notinHB([ * A ] P, HBB) ]
  ACTION [ [ HBB := pushHBB([ * A ] P, HBB) ] ]
  END

  RULE StarBox2 { [ * A ] P } ; Z === Z 
  COND   [ undef_HNx(HNx) ; inHB([ * A ] P, HBB) ]
  END

  RULE TestDia { < ? F > P } ; Z === F ; P ; Z
  COND   [ undefOrP_HNx(HNx, < ? F > P) ]
  ACTION [ [ HNx := testchain_HNx(P);
             HBD := testchain_HBD(P, HBD);
             Hfoc := tstHfoc(< ? F > P, P, Hfoc) ] ]
  END

  RULE SeqDia { < A ; B > P } ; Z === < A > < B > P ; Z
  COND   [ undefOrP_HNx(HNx, < A ; B > P) ]
  ACTION [ [ HNx := testchain_HNx(< A > < B > P);
             HBD := testchain_HBD(< A > < B > P, HBD);
             Hfoc := setHfoc(< A ; B > P, < A > < B > P, Hfoc) ] ]
  END

  RULE Or
        { P v Q } ; Z 
  ====================
      P ; Z ||| Q ; Z

  COND   [ undef_HNx(HNx) ]
  BRANCH [ [ is_true(mrk@1) ] ] 
  BACKTRACK [ mrk := setmrk_beta(mrk@all) ] 
  END

  RULE TestBox
  { [ ? F ] P } ; Z === nnf ( ~ F ) ; Z ||| P ; Z

  COND   [ undef_HNx(HNx) ]
  BRANCH [ [ is_true(mrk@1) ] ] 
  BACKTRACK [ mrk := setmrk_beta(mrk@all) ] 
  END

  RULE UnionDia
  { < A U B > P } ; Z === < A > P ; Z ||| < B > P ; Z

  COND   [ undefOrP_HNx(HNx, < A U B > P) ]
  ACTION [ [ HNx := testchain_HNx(< A > P);
             HBD := testchain_HBD(< A > P, HBD);
             Hfoc := setHfoc(< A U B > P, < A > P, Hfoc) ];
           [ HNx := testchain_HNx(< B > P);
             HBD := testchain_HBD(< B > P, HBD);
             Hfoc := setHfoc(< A U B > P, < B > P, Hfoc) ] ]
  BRANCH [ [ is_true(mrk@1) ] ] 
  BACKTRACK [ mrk := setmrk_beta(mrk@all) ] 
  END

  RULE StarDia1
  { < * A > P } ; Z === P ; Z ||| < A > < * A > P ; Z 

  COND   [ undefOrP_HNx(HNx, < * A > P) ; notinHB(< * A > P, HBD) ]
  ACTION [ [ HNx := testchain_HNx(P);
             HBD := testchain_HBD_Star(P, HBD, < * A > P);
             Hfoc := tstHfoc(< * A > P, P, Hfoc) ];
           [ HNx := testchain_HNx(< A > < * A > P);
             HBD := testchain_HBD_Star(< A > < * A > P, HBD, < * A > P);
             Hfoc := setHfoc(< * A > P, < A > < * A > P, Hfoc) ] ]
  BRANCH [ [ is_true(mrk@1) ] ] 
  BACKTRACK [ mrk := setmrk_beta(mrk@all) ] 
  END

  RULE StarDia2
  { < * A > P } ; Z === Stop

  COND   [ undefOrP_HNx(HNx, < * A > P) ; inHB(< * A > P, HBD) ]
  BACKTRACK [ mrk := true ]
  END

  RULE K 
  { < A > P } ; [ A ] Y ; < B > E ; [ C ] F ; Z
  ==============================================
      P ; Y ||| [ A ] Y ; < B > E ; [ C ] F

  COND   [ loop_check(P, Y, HCr) ]
  ACTION [ [ HCr := push(P, Y, HCr);
             HNx := testchain_HNx(P);
             HBB := emptyset(HBB);
             HBD := emptyset(HBD);
             Hchn := newHchn(< A > P, P, Hfoc, Hchn, Dpt);
             Hfoc := setHfocState(P);
             Dpt := increaseDpt(Dpt) ]; [] ]
  BRANCH [ [ is_false(mrk@1) ] ]
  BACKTRACK [ mrk := setmrk_ext(mrk@all) ]
  END

  RULE Loop
       < A > X ; [ B ] Y
       ==================
             Stop

  BACKTRACK [ mrk := setmrk_loop(< A > X, [ B ] Y, HCr, Hfoc, Hchn, Dpt) ]
  END

END

STRATEGY := 
    let sat = tactic ( (  False ! Id ! StarDia2
                        ! And ! StarBox1 ! StarBox2 !UnionBox ! SeqDia ! SeqBox ! TestDia
                        ! Or ! StarDia1 ! UnionDia ! TestBox) )
    in tactic ( (sat ! K ! Loop)* )

let exit = function
  | true -> "Theorem"
  | false -> "Non-Theorem"

PP := List.map nnf_term
NEG := List.map neg_term
EXIT := exit (mrk@1)

MAIN
