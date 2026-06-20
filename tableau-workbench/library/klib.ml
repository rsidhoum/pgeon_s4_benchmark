
source K

let neg = function formula ( a ) -> formula ( ~ a )

let rec nnf_aux f : [> 'a formula_open] formula_open -> 'a = function
    |formula ( a & b ) -> formula ( {f a} & {f b} )
    |formula ( ~ ( a & b ) ) ->
            formula ( {f formula ( ~ a )} v {f formula ( ~ b )} )

    |formula ( a v b ) -> formula ({f a} v {f b})
    |formula ( ~ ( a v b ) ) ->
            formula ( {f formula ( ~ a )} & {f formula ( ~ b )} )

    |formula ( a <-> b ) ->
            formula ( {f formula ( a -> b )} & {f formula ( b -> a )} )
    |formula ( ~ ( a <-> b ) ) ->
            formula ( {f formula ( ~ (a -> b) )} v {f formula ( ~ (b -> a) )} )

    |formula ( a -> b ) -> f formula ( (~ a) v b )
    |formula ( ~ (a -> b) ) -> f formula ( a & (~ b) )
    |formula ( ~ ~ a ) -> f a

    |formula ( <> a ) -> formula ( <> {f a} )
    |formula ( ~ ( <> a ) ) -> formula ( [] {f ( formula ( ~ a ) )} )
    |formula ( [] a ) -> formula ( [] {f a} )
    |formula ( ~ ( [] a ) ) -> formula ( <> {f ( formula ( ~ a ) )} )

    |formula (Verum) -> formula (Verum)
    |formula (Falsum) -> formula (Falsum)
    |formula (~ Verum) -> formula (Falsum)
    |formula (~ Falsum) -> formula (Verum)

    |formula ( ~ A ) as f -> f
    |formula ( A ) as f -> f

let rec nnf f = nnf_aux nnf f


(*
let nnf_aux f : [> 'a formula_open] formula_open -> 'a = function
    |formula ( <> a ) -> formula ( <> {f a} )
    |formula ( ~ ( <> a ) ) -> formula ( [] {f ( formula ( ~ a ) )} )
    |formula ( [] a ) -> formula ( [] {f a} )
    |formula ( ~ ( [] a ) ) -> formula ( <> {f ( formula ( ~ a ) )} )
    |#formula as x -> Pclib.nnf_aux f x

let rec nnf f = nnf_aux nnf f
*)
