
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

let bdepth n =
    let rec loop acc = function
        |i when i < 0 -> acc 
        |i -> let t = term ( p(100 + i) -> p(99 + i) )
              in loop (t :: acc) (i - 1)
    in list2conj (loop [] (n+1))
;;

let det n =
    let rec loop acc = function
        |i when i < 0 -> acc
        |i ->
                let t = term (
                    p(100 + i) ->
                    (  p(i) -> Box ( p(100 + i) ->   p(i) )) &
                    (~ p(i) -> Box ( p(100 + i) -> ~ p(i) ))
                    )
                in
                loop (t :: acc) (i - 1)
    in list2conj (loop [] n)
;;

let branching n =
    let rec loop acc = function
        |i when i < 0 -> acc
        |i ->
                let t = term (
                    p(100 + i) & ~ p(101 + i) ->
                    (Dia (p(101 + i) & ~ p(102 + i) & p(i + 1)) &
                     Dia (p(101 + i) & ~ p(102 + i) & ~ p(i + 1)) ))
                in
                loop ( t :: acc) (i - 1)
    in list2conj (loop [] (n -1))
;;

(* 6.1 *)
let k_branch_p n =
    let b = term ( [bdepth(n)] & [det(n)] & [branching(n)] ) in
    let rec loop acc = function
        |i when i < 0 -> acc
        |i -> loop ((mbox b i) :: acc) (i - 1)
    in term ( 
        ~ ( p(100) & ~ p(101) & [list2conj (loop [] n)] ) v
        ~ [mbox (term ( p(n / 3 + 1) )) n]
        )
;;

(* 6.2 *)
let k_branch_n n =
    let b = term ( [bdepth(n)] & [det(n)] & [branching(n)] ) in
    let rec loop acc = function
        |i when i < 0 -> acc
        |i -> loop ((mbox b i) :: acc) (i - 1)
    in term ( ~ ( p(100) & ~ p(101) & [list2conj (loop [] n)] ) )
;;

Common.provable := k_branch_p ;;
Common.notprovable := k_branch_n ;;

