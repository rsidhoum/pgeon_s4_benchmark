
source K

let rec boolean t = 
    let aux = function
        |formula (a & b) when a = b -> a
        |formula (a v b) when a = b -> a
        |formula (Verum & b)  -> b 
        |formula (b & Verum)  -> b
        |formula (Falsum & b) -> formula (Falsum)
        |formula (b & Falsum) -> formula (Falsum)
        |formula (Verum v b)  -> formula (Verum)
        |formula (b v Verum)  -> formula (Verum)
        |formula (Falsum v b) -> b
        |formula (b v Falsum) -> b
        |formula (<> Falsum)  -> formula (Falsum)
        |formula ([] Falsum)  -> formula (Falsum)
        |formula (~ Verum)    -> formula (Falsum)
        |formula (~ Falsum)   -> formula (Verum)
        |a -> a
    in match t with
    |formula (a & b) -> aux formula ( {boolean (aux a)} & {boolean (aux b)} )
    |formula (a v b) -> aux formula ( {boolean (aux a)} v {boolean (aux b)} )
    |formula (<> a) -> aux formula ( <> {boolean (aux a)} )
    |formula ([] a) -> aux formula ( [] {boolean (aux a)} )
    |formula (~ a)   -> aux formula ( ~ {boolean (aux a)} )
    |a -> aux a
;;

(*
let nnf f =
    let rec aux = function
        |term ( a & b ) as f -> Pcopt.order aux f
        |term ( ~ ( a & b ) ) -> aux term ( ~ a  v ~ b )
        |term ( a v b ) as f -> Pcopt.order aux f
        |term ( ~ ( a v b ) ) -> aux term ( ~ a & ~ b )
        |term ( a <-> b ) ->
                aux term ( ( a -> b ) & ( b -> a ) )
        |term ( ~ ( a <-> b ) ) ->
                aux term ( ( ~ (a -> b) ) v ( ~ (b -> a) ) )
        |term ( a -> b ) -> aux term ( (~ a) v b )
        |term ( ~ (a -> b) ) -> aux term ( a & (~ b) )
        |term ( ~ ~ a ) -> aux a
        |term ( ~ Atom ) as f -> (0,f)
        |term ( Atom ) as f   -> (0,f)
        |term ( Constant ) as f -> (0,f)
        |term (~ Constant) as f -> (0,f)

        |term ( Dia a ) -> let (d,t) = aux a in (d,term ( Dia t ))
        |term ( ~ ( Dia a ) ) -> aux term ( Box ~ a )
        |term ( Box a ) -> let (d,t) = aux a in (d,term ( Box t ))
        |term ( ~ ( Box a ) ) -> aux term ( Dia ~ a )

        |f -> failwith (Printf.sprintf "aux:%s" (Twblib.sof(f)))
    in let (_,f') = aux f in boolean f'
;;

let rec cnf t =
    let rec distrib = function
        |t1, term ( t2 & t3 ) -> term ([distrib(t1,t2)] & [distrib(t1,t3)])
        |term (t1 & t2), t3 -> term ([distrib(t1,t3)] & [distrib(t2,t3)])
        |t1,t2 -> term (t1 v t2)
    in
    let rec conjnf t =
        match t with
        |term (t1 & t2) -> term ([conjnf(t1)] & [conjnf(t2)])
        |term (t1 v t2) -> distrib (conjnf(t1),conjnf(t2))
        |term (Box t1) -> term ( Box [cnf t1] )
        |term (Dia t1) -> term ( Dia [cnf t1] )
        |_ -> t
in conjnf t
;;
*)

let rec simpl nnf phi a =
    (* Printf.printf "Simplification ! %s[%s]\n" (formula_printer a) 
    (formula_printer phi); *)
    let rec aux phi a = match a with
        |formula (~ b) when b = a -> formula(Falsum) 
        |formula (~ b)   -> formula ( ~ {aux phi b} )
        |formula (b & c) -> formula ( {aux phi b} & {aux phi c} )
        |formula (b v c) -> formula ( {aux phi b} v {aux phi c} )
        |formula ([] b) ->
                begin match phi with
                |formula ([] phi') -> formula ( [] {aux phi' b} )
                |_ -> a
                end
        |formula (<> b) ->
                begin match phi with
                |formula ([] phi') -> formula ( <> {aux phi' b} )
                |_ -> a
                end
        |_ when phi = a -> formula(Verum)
        |_ when phi = (nnf (formula ( ~ a ))) -> formula(Falsum)
        |_ -> a
    in
    let r = boolean (aux phi a) in
    (* Printf.printf "Result: %s\n\n" (formula_printer r) ; *)
    r
;;
(*
let rec simpl4 phi a =
(*    Printf.printf "Simplification ! %s[%s]\n" (Twblib.sof(a)) (Twblib.sof(phi)); *)
    let rec aux phi a = match a with
        |term (~ b) when b = a -> term(Falsum) 
        |term (~ b)   -> term ( ~ [aux phi b] )
        |term (b & c) -> term ( [aux phi b] & [aux phi c] )
        |term (b v c) -> term ( [aux phi b] v [aux phi c] )
        |term (Box b) ->
                begin match phi with
                |term (Box phi') -> term ( Box [aux phi' (aux phi b)] )
                |_ -> a
                end
        |term (Dia b) ->
                begin match phi with
                |term (Box phi') -> term ( Dia [aux phi' (aux phi b)] )
                |_ -> a
                end
        |_ when phi = a -> term(Verum)
        |_ when phi = (nnf (term ( ~ a ))) -> term(Falsum)
        |_ -> a
    in
    let r = boolean (aux phi a) in
(*    Printf.printf "Result: %s\n\n" (Twblib.sof(r)) ;  *)
    r
;;
*)
