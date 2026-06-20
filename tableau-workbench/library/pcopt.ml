
source Pc

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
        |formula (~ Verum)    -> formula (Falsum)
        |formula (~ Falsum)   -> formula (Verum)
        |a -> a
    in match t with
    |formula (a & b) -> aux formula ( {boolean (aux a)} & {boolean (aux b)} )
    |formula (a v b) -> aux formula ( {boolean (aux a)} v {boolean (aux b)} )
    |formula (~ a)   -> aux formula ( ~ {boolean (aux a)} )
    |a -> aux a
;;

let rec simpl nnf phi a =
    (* Printf.printf "Simplification ! %s[%s]\n" (formula_printer a) 
    (formula_printer phi); *)
    let rec aux phi a = match a with
        |formula (~ b) when b = a -> formula(Falsum) 
        |formula (~ b)   -> formula ( ~ {aux phi b} )
        |formula (b & c) -> formula ( {aux phi b} & {aux phi c} )
        |formula (b v c) -> formula ( {aux phi b} v {aux phi c} )
        |_ when phi = a -> formula(Verum)
        |_ when phi = (nnf (formula ( ~ a ))) -> formula(Falsum)
        |_ -> a
    in
    let r = boolean (aux phi a) in
    (* Printf.printf "Result: %s\n\n" (formula_printer r) ; *)
    r
;;

(*
source Pcbj

(* workd if f is in nnf *)
let rec weigth = function
    | formula ( a & b ) -> (weigth a) * (weigth b) 
    | formula ( a v b ) -> 1 + (weigth a) + (weigth b) 
    |_ -> 0

let cmp a b = Pervasives.compare (weigth a) (weigth b) 

(* raughly MOMS : less disjunct at the front *)
let rec order aux = function
    | formula ( a & b ) -> 
        let (d1,t1) = aux a in
        let (d2,t2) = aux b in
        let d = d1 * d2 in
        begin match Pervasives.compare d1 d2 with
        |i when i > 0 -> d,  formula ( t2 & t1 )
        |i when i < 0 -> d,  formula ( t1 & t2 )
        |_ ->
                begin match Pervasives.compare a b with
                |i when i > 0 -> d,  formula ( t2 & t1 )
                |i when i < 0 -> d,  formula ( t1 & t2 ) 
                |_ -> d, t1
                end
        end
    | formula ( a v b ) -> 
        let (d1,t1) = aux a in
        let (d2,t2) = aux b in
        let d = 1 + d1 + d2 in
        begin match Pervasives.compare d1 d2 with
        |i when i > 0 -> d,  formula ( t2 v t1 )
        |i when i < 0 -> d,  formula ( t1 v t2 )
        |_ ->
                begin match Pervasives.compare a b with
                |i when i > 0 -> d,  formula ( t2 v t1 )
                |i when i < 0 -> d,  formula ( t1 v t2 ) 
                |_ -> d, t1
                end
        end
    |_ -> failwith "order"

let nnf f =
    let rec aux = function
        | formula ( a & b ) as f -> order aux f
        | formula ( ~ ( a & b ) ) -> aux  formula ( ~ a  v ~ b )
        | formula ( a v b ) as f -> order aux f
        | formula ( ~ ( a v b ) ) -> aux  formula ( ~ a & ~ b )
        | formula ( a <-> b ) ->
                aux  formula ( ( a -> b ) & ( b -> a ) )
        | formula ( ~ ( a <-> b ) ) ->
                aux  formula ( ( ~ (a -> b) ) v ( ~ (b -> a) ) )
        | formula ( a -> b ) -> aux  formula ( (~ a) v b )
        | formula ( ~ (a -> b) ) -> aux  formula ( a & (~ b) )
        | formula ( ~ ~ a ) -> aux a
        | formula ( ~ A ) as f -> (0,f)
        | formula ( A ) as f   -> (0,f)
(*        | formula (  ) as f -> (0,f)
        | formula (~ Constant) as f -> (0,f) *)
        |f -> failwith (Printf.sprintf "aux:%s" (formula_printer f))
    in let (_,f') = aux f in f'

let rec boolean t =
    let aux = function
        | formula (a & b) when a = b -> a
        | formula (a v b) when a = b -> a
        | formula (Verum & b)  | formula (b & Verum)  -> b
        | formula (Falsum & b) | formula (b & Falsum) -> formula (Falsum)
        | formula (Verum v b)  | formula (b v Verum)  -> formula (Verum)
        | formula (Falsum v b) | formula (b v Falsum) -> b
        | formula (~ Verum)  ->  formula (Falsum)
        | formula (~ Falsum) ->  formula (Verum)
        |a -> a
    in match t with
    | formula (a & b) -> aux  formula ( {boolean (aux a)} & {boolean (aux b)} )
    | formula (a v b) -> aux  formula ( {boolean (aux a)} v {boolean (aux b)} )
    | formula (~ a)   -> aux  formula ( ~ {boolean (aux a)} )
    |a -> aux a


let rec simpl phi a =
(*    Printf.printf "Simplification ! %s[%s]\n" (Twblib.sof(a)) (Twblib.sof(phi)); *)
    let rec aux phi a = match a with
        | formula (~ b) when b = a ->  formula(Falsum)
        | formula (~ b)   ->  formula ( ~ {aux phi b} )
        | formula (b & c) ->  formula ( {aux phi b} & {aux phi c} )
        | formula (b v c) ->  formula ( {aux phi b} v {aux phi c} )
        |_ when phi = a ->  formula(Verum)
        |_ when phi = (nnf ( formula ( ~ a ))) ->  formula(Falsum)
        |_ -> a
    in
    let r = boolean (aux phi a) in
(*    Printf.printf "Result: %s\n\n" (Twblib.sof(r)) ;  *)
    r

*)

let inc idx = idx + 1 

let addlabel (tl1,tl2) =
    match List.hd tl1,List.hd tl2 with
    |`LabeledFormula(l1,t1),`LabeledFormula(l2,t2) -> ExtList.list_uniq(l1@l2)
    |_ -> failwith "backjumping"

let simpbj simpf (tl,sl) =
    open_bt_list (
        List.map( function
            |expr (l : t) ->
                    let (rl,rt) =
                        List.fold_left(fun (il1,a) s ->
                            match List.hd s with
                            |expr (il2 : phi) ->
                                let a' = simpf phi a in
                                if a' = a then (il1,a)
                                else (il1@il2,a')
                            |_ -> failwith "simplbj"
                        ) (l,t) sl
                    in expr (ExtList.list_uniq rl : rt)
            |_ -> failwith "simpl"
        ) tl
    )

let fixlabel (idx,tl) =
    List.map( function
        |expr (l : t) -> expr (idx::l : t)
        |_ -> failwith "fixlabel"
    ) tl

let backjumping (idx,intlist) = List.mem idx intlist ;;

let mergelabel (intll, status) =
    if status = "Open" then [] else ExtList.list_uniq(List.flatten intll)

