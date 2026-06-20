
source Ub

let rec nnf_term f =
    match f with
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

    |formula ( ~ P ) as f -> f
    |formula ( P ) as f -> f

    |formula ( AX a ) -> 
            let x = nnf_term a
            in formula ( AX x )
            
    |formula ( ~ ( AX a ) ) -> 
            let x = nnf_term ( formula ( ~ a ) )
            in formula ( EX x )

    |formula ( EX a ) -> 
            let x = nnf_term a
            in formula ( EX x )
            
    |formula ( ~ ( EX a ) ) -> 
            let x = nnf_term ( formula ( ~ a ) )
            in formula ( AX x )
            
    |formula ( ~ AG a ) ->
            nnf_term formula ( EF ~ a )
            
    |formula ( ~ EG a ) ->
            nnf_term formula ( AF ~ a )
 
    |formula ( AG a ) -> 
            let x = nnf_term formula ( a )
            in formula ( AG x )

    |formula ( EG a ) -> 
            let x = nnf_term formula ( a )
            in formula ( EG x )

    |formula ( ~ EF a ) -> 
            let x = nnf_term formula ( ~ a )
            in formula ( AG x )

    |formula ( ~ AF a ) -> 
            let x = nnf_term formula ( ~ a )
            in formula ( EG x )

    |formula ( EF a ) -> 
            let x = nnf_term formula ( a )
            in formula ( EF x )

    |formula ( AF a ) -> 
            let x = nnf_term formula ( a )
            in formula ( AF x )

    |formula ( ~ Falsum ) -> formula ( Verum )
    |formula ( ~ Verum ) -> formula ( Falsum )

    |formula ( Falsum ) -> formula ( Falsum )
    |formula ( Verum ) -> formula ( Verum )


let neg_term = function formula ( a ) -> formula ( ~ a ) 
