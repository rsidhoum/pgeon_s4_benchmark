
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

let rec l2 = function
  | 0 -> term ( Falsum )
  | i -> term (Box [l2 (i-1)] v p(1) v p(2) v p(3) v p(4))
;;

let l i =
    match i with
    |i when i mod 4 = 0 -> term ( axiomGrz1{ [l2(i/4)] / p(0)} )
    |i when i mod 4 = 1 -> term ( axiomGrz1{ Box [l2(i/4)] v p(1) / p(0)} )
    |i when i mod 4 = 2 -> term ( axiomGrz1{ Box [l2(i/4)] v p(1) v p(2) / p(0)} )
    |i -> term ( axiomGrz1{ Box [l2(i/4)] v p(1) v p(2) v p(3) / p(0)} )
;;

let k_grz_p n = 
    let c = term (Box ( p(2) -> Box p(2)) -> p(2)) in
    let d = loop l 1 (n-1) in
    (* we have to write this formula using all these variable because
     * of a syntactic restriction in the parser : TODO *)
    let t0 = term ( axiomA4{c / p(0)} ) in
    let t1 = term ( axiomGrz{p(2) / p(0)} ) in
    let t2 = term ( axiomGrz{c & t0 / p(0)} ) in
    let t3 = term ( axiomGrz1{p(1) / p(0)} ) in
    let t4 = term ( axiomGrz1{p(2) / p(0)} ) in
    let t5 = term ( axiomGrz1{p(3) / p(0)} ) in
    term ( Box t1 & [list2conj d] & t2 -> t3 v t4 v t5 )
;;

let k_grz_n n = term (Falsum) ;;

Common.provable := k_grz_p ;;
Common.notprovable := k_grz_n ;;

