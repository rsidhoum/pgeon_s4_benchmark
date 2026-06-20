
CONNECTIVES
  DImp, "_<->_", Two;
  And, "_&_",  One;
  Or,  "_v_",  One;
  Imp, "_->_", One;
  Not, "~_",   Zero;
  Box, "Box_", Zero;
  Dia, "Dia_", Zero;
  Falsum, Const;
  Verum, Const
END

open Twblib
open Klib
open Pcopt

HISTORIES
(DIAMONDS : Set of Formula := new Set.set);
(BOXES : Set of Formula := new Set.set);
(Idx : Int := new Set.set default 0);
(bj : ListInt := new Set.set default [])
END

let nnf_term l = Basictype.map Kopt.nnf l ;; 

let simpl (tl,sl) = Pcopt.simpbj Kopt.simpl4 (tl,sl);;
let addlabelf = function
    `LabeledFormula(l,_) -> l
    |_ -> failwith "addlabelf"
;;

TABLEAU

  RULE S4
  { Dia a } ; Box x ; z
  ----------------------
  a ; simpl(x,[a]) ; Box x

  COND notin(Dia a, DIAMONDS)
  ACTION [ DIAMONDS := add(Dia a,DIAMONDS) ]
  BACKTRACK [ bj := mergelabel(bj@all, status@last) ]
  END (cache)

  RULE S4H
  { Dia a } ; Box x ; Dia y ; z
  ===============================
      a ; simpl(x,[a]) ; Box x || Dia y ; Box x

  COND notin(Dia a, DIAMONDS)

  BRANCH [ not_emptylist(Dia y) ]
  ACTION [
      [ DIAMONDS := add(Dia a,DIAMONDS);
        DIAMONDS := add(Dia y,DIAMONDS)];

      [ DIAMONDS := add(Dia a,DIAMONDS) ]
  ]

  BACKTRACK [ bj := mergelabel(bj@all, status@last) ]
  END (cache)

  RULE T
  { Box a }
  =========
   a ; Box a

  COND notin(a, BOXES)

  ACTION [
      BOXES    := add(a,BOXES);
      DIAMONDS := emptyset (DIAMONDS) ]
  END

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

    BACKTRACK [ bj := addlabelf(Falsum) ]
  END

  RULE And
  { a & b } ; x
  ==========
    simpl(a,[b]) ; simpl(b,[a]) ; simpl(x,[a;b])
  END
  
  RULE Or
  { a v b } ; x
 =================================
     fixlabel(Idx,a) ; simpl(x,[fixlabel(Idx,a)]) |
     simpl(fixlabel(Idx,b),[nnf_term(~ a)]) ; simpl(x,[fixlabel(Idx,b);nnf_term(~ a)])
   
  ACTION    [[ Idx := inc(Idx) ]; [ Idx := inc(Idx) ]]
  BRANCH    [ backjumping(Idx, bj@1) ]
  BACKTRACK [ bj := mergelabel(bj@all, status@last) ]

  END

END

PP := Kopt.nnf
NEG := neg

let saturate = tactic ( (False|Id|And|T|Or)* )

STRATEGY := ( ( saturate ; S4H )* )

