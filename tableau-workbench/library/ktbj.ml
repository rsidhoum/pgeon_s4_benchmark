
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

HISTORIES
(BOXES : Set of Formula := new Set.set);
(Idx : Int := new Set.set default 0);
(bj : ListInt := new Set.set default [])
END

let nnf_term l = Basictype.map Kopt.nnf l ;; 

open Twblib
open Klib
open Pcopt

TABLEAU

  RULE K
  { Dia a } ; Box x ; z
  ----------------------
    a ; x

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

let saturate = tactic ( (False|Id|And|T|Or)* )

STRATEGY := ( ( saturate ; K )* )

