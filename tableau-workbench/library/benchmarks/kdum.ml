
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

let k_dum_p n =
    let t1 = term (axiomA4{ (Box (p(0) -> Box p(0)) -> p(0)) / p(0) } ) in
    let t2 = term (axiomDum{ (p(0) -> Box p(0)) / p(0) }) in
    let c = term (t1 & Box axiomA4 & axiomDum & t2) in
    let d1 = loop (mbox term (Box axiomA4 & axiomDum)) 1 (n/2) in
    let d2 = loop (mdia term (~ (Box axiomA4 & axiomDum))) ((n/2)+2) (n-1)
    in term (
        [list2conj(d1)] &
        ~ [mbox axiomDum1 ((n/2)+1)] ->
        [mdia term (~ c) ((n/2)+1)] v
        [list2disj d2]
    )
;;

let k_dum_n n =
    let t1 = term (axiomA4{ (Box (p(0) -> Box p(0)) -> p(0)) / p(0) } ) in
    let t2 = term (axiomDum4{ (p(0) -> Box p(0)) / p(0) }) in
    let c = term (t1 & Box axiomA4 & axiomDum4 & t2) in
    let d1 = loop (mbox term (Box axiomA4 & axiomDum4)) 1 (n/2) in
    let d2 = loop (mdia term (~ (Box axiomA4 & axiomDum4))) ((n/2)+2) (n-1)
    in term (
        [list2conj(d1)] &
        ~ [mbox axiomDum (n+1)] ->
        [mdia term (~ c) (n+1)] v
        [list2disj d2]
    )
;;

