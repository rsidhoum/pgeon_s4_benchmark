
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
(BOXES : Set of Formula := new Set.set);
(Idx : Int := new Set.set default 0);
(bj : ListInt := new Set.set default [])
END

let nnf_term l = [`LabeledFormula([],Kopt.nnf (Basictype.unbox(List.hd l)))] ;;

let simpl (tl,sl) = Pcopt.simpbj Kopt.simpl (tl,sl);;
let addlabelf = function
    `LabeledFormula(l,_) -> l
    |_ -> failwith "addlabelf"
;;

TABLEAU

  RULE K
  { Dia a } ; Box x ; z
  ----------------------
  a ; simpl(x,[a])

  ACTION [ BOXES := clear(BOXES) ]
  BACKTRACK [ bj := mergelabel(bj@all, status@last) ]
  END (cache)

  RULE T
  { Box a }
  =========
     a ; Box a

  COND notin(a, BOXES)

  ACTION [ BOXES := add(a,BOXES) ]
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

STRATEGY := ( ( saturate | K )* )

