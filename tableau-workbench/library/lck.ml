
CONNECTIVES [
"~";"&";"v";"->";"<->";
"[";"]";"<";">";
"<E>";"[E]";
"<C>";"[C]" ]
GRAMMAR
idx := One | Two ;;
formula :=
     ATOM | Verum | Falsum
    | idx
    | formula & formula
    | formula v formula
    | formula -> formula
    | formula <-> formula
    | <E> formula
    | [E] formula
    | <C> formula
    | [C] formula
    | [ idx ] formula
    | < idx > formula
    | ~ formula
;;

expr := formula ;;
END

HISTORIES
  Fev : FormulaSet.set := new FormulaSet.set;
  Br  : ListFormulaSet.olist := new ListFormulaSet.olist
END

VARIABLES
  uev : FormulaIntSet.set := new FormulaIntSet.set;
  fev : FormulaIntSet.set := new FormulaIntSet.set;
  status : string := "Undef"
END

open Twblib
open LckRewrite
open LckFunctions

TABLEAU

  RULE Id
  { a } ; { ~ a } == Stop
  BACKTRACK [ uev := setclose (Br) ]
  END
  
  RULE False { Falsum } ; Z == Stop
  BACKTRACK [ uev := setclose (Br) ]
  END

  RULE CDia
      { <C> P }
  ===================
   <E> P ||| <E> <C> P

  ACTION [ [ Fev := add(<C> P,Fev) ] ; [] ]
  BRANCH [ [ not_empty(uev@1) ] ] 
  BACKTRACK [ uev := setuev_beta(uev@1, uev@2, Br) ]
  END

  RULE EDia
      {  <E> P }
  ===================
   <One> P ||| <Two> P

  BRANCH [ [ not_empty(uev@1) ] ] 
  BACKTRACK [ uev := setuev_beta(uev@1, uev@2, Br) ] 
  END

  RULE K
  { < I > P } ; [ I ] X ;  Z
  ----------------------
          P ; X

  COND [ loop_check(P, X, Br) ]
  ACTION [
      Fev := emptyset(Fev);
      Br  := push(P, X, Fev, Br)
  ]
  BRANCH [ [ not_false(uev@1) ]
  BACKTRACK [ uev := setuev_pi(uev@1, uev@2, Br) ]
  END

  RULE Loop <One> X1 ; <Two> X2 ; [One] Y1 ; [Two] Y2 == Stop
  BACKTRACK [ uev := setuev_loop(X1, Y1, X2, Y2, Fev, Br) ]
  END

  RULE Or { A v B } == A ||| B
  BRANCH [ [ not_empty(uev@1) ] ] 
  BACKTRACK [ uev := setuev_beta(uev@1, uev@2, Br) ] 
  END

  RULE And A & B == A ; B END
  RULE EBox [E] P == [One] P ; [Two] P END
  RULE CBox [C] P == [E] P ; [E] [C] P END
  
END

let exit (uev) = match uev#elements with
    |[] -> "Open" 
    |[formula ( Falsum ),_] -> "Closed"
    |_ -> "Closed"
  
PP := nnf 
NEG := List.map neg
EXIT := exit (uev@1)

let saturation = tactic ( (Id! And! Or! Edia! Cbox! Ebox! Cdia! False) )
let modal = tactic ( (saturation)* ; ( K ! Loop) )

STRATEGY tactic ( (modal)* )

