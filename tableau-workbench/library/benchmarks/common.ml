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

let provable = ref (fun n ->
    if n > 0 then term (Verum) else failwith "provable")
let notprovable = ref (fun n ->
    if n > 0 then term (Falsum) else failwith "notprovable")


(* mbox a n = Box ... Box a (n Boxes) *)
let rec mbox a = function
    |0 -> a
    |n -> mbox (term ( Box a )) (n-1)
;;

(* mdia a n = Dia ... Dia a (n Dias) *)
let rec mdia a = function
    |0 -> a
    |n -> mdia (term ( Dia a )) (n-1)
;;

let rec list2conj = function
    |[] -> term ( Verum )
    |[h] -> h
    |h::t -> term (h & [list2conj t])
;;

let rec list2disj = function
    |[] -> term ( Falsum )
    |[h] -> h
    |h::t -> term (h v [list2disj t])
;;

let rec modaldepth = function
    |term ( Verum ) -> 0
    |term ( Falsum ) -> 0
    |term ( Dia a )
    |term ( Box a ) -> (modaldepth a) + 1
    |term ( ~ a ) -> modaldepth a
    |term ( a & b )
    |term ( a v b )
    |term ( a -> b )
    |term ( a <-> b ) -> max ( modaldepth a ) ( modaldepth b )
    | _ -> failwith "modaldepth"
;;

let rec length = function
    |term ( Verum ) -> 1
    |term ( Falsum ) -> 1
    |term ( Dia a )
    |term ( Box a )
    |term ( ~ a ) -> (length a) + 1
    |term ( a & b )
    |term ( a v b )
    |term ( a -> b )
    |term ( a <-> b ) -> ( length a ) + ( length b ) + 1
    | _ -> failwith "length"
;;

let rec nnf = function
    | term (Verum) -> term (Verum)
    | term (Falsum) -> term (Falsum)
    | term ( Dia a ) -> term (Dia [nnf a])
    | term ( Box a ) -> term (Box [nnf a])
    | term ( a & b ) -> term ([nnf a] & [nnf b])
    | term ( a v b ) -> term ([nnf a] v [nnf b])
    | term ( a -> b ) -> term ([nnfneg a] v [nnf b])
    | term (~ a) -> nnfneg a
    | term (a) -> term (a)
  and nnfneg = function
    | term (Verum) -> term (Falsum)
    | term (Falsum) -> term (Verum)
    | term (Dia a) -> term (Box [nnfneg a])
    | term (Box a) -> term (Dia [nnfneg a])
    | term (a & b) -> term ([nnfneg a] v [nnfneg b])
    | term (a v b) -> term ([nnfneg a] & [nnfneg b])
    | term (a -> b) -> term ([nnf a] & [nnfneg b])
    | term (~ a) -> nnf a
    | term (a) -> term (~ a)
;;

let axiomD  = term (Box p(0) -> Dia p(0)) ;;
let axiomT  = term (Box p(0) -> p(0)) ;;
let axiomD2 = term (Dia Verum) ;;
let axiomA4 = term (Box p(0) -> Box Box p(0)) ;;
let axiomB  = term (p(0) -> Box Dia p(0)) ;;

let axiomGrz  = term (Box (Box (p(0) -> Box p(0)) -> p(0)) -> p(0) )
let axiomGrz1 = term (Box (Box (p(0) -> Box p(0)) -> p(0)) -> Box p(0) )

let axiomDum =
    term (Box (Box(p(0) -> Box p(0)) -> p(0)) -> ( (Dia Box p(0)) -> p(0) ) )
;;
let axiomDum1 =
    term (Box (Box(p(0) -> Box p(0)) -> p(0)) -> ( (Dia Box p(0)) -> Box p(0) ) )
;;
let axiomDum4 =
    term (Box (Box(p(0) -> Box p(0)) -> p(0)) -> ( (Dia Box p(0)) -> p(0) v Box p(0) ) )
;;

let loop f i n =
    let rec aux acc = function
        |i when i >= n -> acc
        |i -> aux ((f i)::acc) (i+1)
    in aux [] i
;;

let rec range i n = if i > n then [] else i :: range (i+1) n ;;


