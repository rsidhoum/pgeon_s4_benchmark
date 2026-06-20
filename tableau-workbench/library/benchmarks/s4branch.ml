
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

open Common
open Kbranch

(* 8.4 *)
let s4_branch_n n =
    let t = term ([bdepth n] & [det n] & [branching n])
    in term ( ~ p(100) & ~ p(101) & Box t )
;;

(* 8.3 *)
let s4_branch_p n =
    let t = term ([bdepth n] & [det n] & [branching n])
    in term (~ ( p(100) & ~ p(101) & Box t ) v ~ Box p(n / 3 + 1) )
;;

Common.provable := s4_branch_p ;;
Common.notprovable := s4_branch_n ;;

