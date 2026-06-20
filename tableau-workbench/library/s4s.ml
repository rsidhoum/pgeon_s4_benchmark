
CONNECTIVES
  DImp, "_<->_", Two;
  And, "_&_",  One;
  Or,  "_v_",  One;
  Imp, "_->_", One;
  Not, "~_",   Zero;
  Dia, "Dia_", Zero;
  Box, "Box_", Zero;
  Falsum, Const;
  Verum, Const
END

HISTORIES
  (DIAMONDS : Set of Formula := new Set.set);
  (BOXES : Set of Formula := new Set.set)
END

SIMPLIFICATION := Kopt.simpl4
let nnf_term l = ([],Kopt.nnf (Basictype.unbox(List.hd l))) ;;
let nnf = Kopt.nnf ;;

open Twblib
open Klib

TABLEAU

  RULE S4
  { Dia a } ; Box x ; z
  ----------------------
  a ; x[a] ; Box x
  
  COND notin(Dia a, DIAMONDS)
  ACTION [ DIAMONDS := add(Dia a,DIAMONDS) ]
  END (cache)

  RULE S4H
  { Dia a } ; Box x ; Dia y ; z
  ===============================
      a ; x[a] ; Box x || Dia y ; Box x

  COND notin(Dia a, DIAMONDS)
  BRANCH [ not_emptylist(Dia y) ]
  ACTION [
      [ DIAMONDS := add(Dia a,DIAMONDS);
        DIAMONDS := add(Dia y,DIAMONDS)];

      [ DIAMONDS := add(Dia a,DIAMONDS) ]
  ]

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
  END
  
  RULE False
    Falsum
  =========
    Close
  END

  RULE And
  { a & b } ; x
  =======================
    a[b] ; b[a] ; x[a][b]
  END
  
  RULE Or
  { a v b } ; x
 ================================
  a ; x[a] | b[nnf_term(~ a)] ; x[b][nnf_term(~ a)]
  END

END

PP := Kopt.nnf
NEG := neg

let saturation = tactic ( (False|Id|And|T|Or)* )

STRATEGY ( saturation ; S4H )*
