
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

(* 7.4 *)
let kt_branch_n n =
    let t = term ([bdepth n] & [det n] & [branching n])
    in term ( ~ p(100) & ~ p(101) & [mbox t n] )
;;

(* 7.3 *)
let kt_branch_p n = 
    let t = term ( p(n / 3 + 1) ) in
    term ([kt_branch_n n] v ~ [mbox t n] )
;;

provable := kt_branch_p ;;
notprovable := kt_branch_n ;;
