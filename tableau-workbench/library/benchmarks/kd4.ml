
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

(* 6.3 *)
let k_d4_p_aux n i = term (
      [mbox axiomT n] v
    ~ [mbox axiomD2 i] v
    ~ [mbox axiomA4 i] v
    ~ [mbox term ( axiomA4{Dia p(0)/p(0)} ) i] v
    ~ [mbox axiomB i] v
    ~ [mbox term ( axiomB{~ p(0)/p(0)} ) i] 
)
;;

let k_d4_p n = nnf (list2disj (List.map (k_d4_p_aux n) (range 1 n))) ;;

(* 6.4 *)
let k_d4_p_aux n i = term (
    [mbox term (Box p(0) v Box Dia ~ p(0)) n] v
    ~ [mbox axiomD2 i] v
    ~ [mbox axiomA4 i] v
    ~ [mbox term ( axiomA4{Dia p(0)/p(0)} ) i] v
    ~ [mbox axiomD i] v
    ~ [mbox term ( axiomA4{Dia p(0) -> p(0)/p(0)} ) i] v
    ~ [mbox term ( axiomA4{Box p(0) -> p(0)/p(0)} ) i] 
)
;;

let k_d4_n n = nnf (list2disj (List.map (k_d4_p_aux n) (range 1 n))) ;;

Common.provable := k_d4_p ;;
Common.notprovable := k_d4_n ;;

