
source Pltl

let rec nnf_term = function
    |formula ( a & b ) ->
        let x = nnf_term a
        and y = nnf_term b
        in formula ( x & y )

    |formula ( ~ ( a & b ) ) ->
        let x = nnf_term formula ( ~ a )
        and y = nnf_term formula ( ~ b )
        in formula ( x v y )

    |formula ( a v b ) ->
            let x = nnf_term a
            and y = nnf_term b
            in formula ( x v y )

    |formula ( ~ ( a v b ) ) ->
            let x = nnf_term formula ( ~ a )
            and y = nnf_term formula ( ~ b )
            in formula ( x & y )

    |formula ( a <-> b ) ->
            let x = nnf_term formula ( a -> b )
            and y = nnf_term formula ( b -> a )
            in formula ( x & y )

    |formula ( ~ ( a <-> b ) ) ->
            let x = nnf_term formula ( ~ (a -> b) )
            and y = nnf_term formula ( ~ (b -> a) )
            in formula ( x v y )

    |formula ( a -> b ) ->
            nnf_term formula ( (~ a) v b )

    |formula ( ~ (a -> b) ) ->
            nnf_term formula ( a & (~ b) )

    |formula ( ~ ~ a ) -> nnf_term a

    |formula ( ~ A ) as f -> f
    |formula ( A ) as f -> f

    |formula ( X a ) -> 
            let x = nnf_term a
            in formula ( X x )
            
    |formula ( ~ ( X a ) ) -> 
            let x = nnf_term ( formula ( ~ a ) )
            in formula ( X x )
            
    |formula ( ~ G a ) ->
            nnf_term formula ( F ~ a )
    |formula ( G a ) -> 
            let x = nnf_term formula ( a )
            in formula ( G x )

    |formula ( ~ F a ) ->
            nnf_term formula ( G ~ a )
    |formula ( F a ) ->
            nnf_term formula ( Verum Un a )

    |formula ( ~ (a Bf b) ) ->
            nnf_term formula ( ~ a Un b )
    |formula ( a Bf b ) ->
            let x = nnf_term formula ( a )
            and y = nnf_term formula ( b )
            in formula ( x Bf y )

    |formula ( ~ (a Un b) ) ->
            nnf_term formula ( ~ a Bf b )
    |formula ( a Un b ) ->
            let x = nnf_term formula ( a )
            and y = nnf_term formula ( b )
            in formula ( x Un y )

    |formula ( ~ Falsum ) -> formula ( Verum )
    |formula ( ~ Verum ) -> formula ( Falsum )
    |formula ( Falsum ) -> formula ( Falsum )
    |formula ( Verum ) -> formula ( Verum )

let neg_term = function formula ( a ) -> formula ( ~ a ) 
