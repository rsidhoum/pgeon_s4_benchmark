source CtlMark

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
            
    |formula ( ~ AG a ) -> nnf_term formula ( E Verum U ~ a )
    |formula ( ~ EG a ) -> nnf_term formula ( A Verum U ~ a )
 
    |formula ( ~ EF a ) -> nnf_term formula ( ~ E Verum U a )
    |formula ( ~ AF a ) -> nnf_term formula ( ~ A Verum U a )

    |formula ( ~ ( E a U b ) ) -> nnf_term formula ( A ~ a B b )
    |formula ( ~ ( A a U b ) ) -> nnf_term formula ( E ~ a B b )

    |formula ( ~ ( E a B b ) ) -> nnf_term formula ( A ~ a U b )
    |formula ( ~ ( A a B b ) ) -> nnf_term formula ( E ~ a U b )

    |formula ( ~ ( AX a ) ) -> nnf_term formula ( EX ~ a )
    |formula ( ~ ( EX a ) ) -> nnf_term formula ( AX ~ a )

    |formula ( AG a ) -> nnf_term formula ( ~ E Verum U ~ a )
    |formula ( EG a ) -> nnf_term formula ( ~ A Verum U ~ a )

    |formula ( EF a ) -> nnf_term formula ( E Verum U a )
    |formula ( AF a ) -> nnf_term formula ( A Verum U a )

    |formula ( E a U b ) -> formula ( E {nnf_term a} U {nnf_term b} )
    |formula ( A a U b ) -> formula ( A {nnf_term a} U {nnf_term b} )

    |formula ( E a B b ) -> formula ( E {nnf_term a} B {nnf_term b} )
    |formula ( A a B b ) -> formula ( A {nnf_term a} B {nnf_term b} )

    |formula ( AX a ) -> formula ( AX {nnf_term a} )
    |formula ( EX a ) -> formula ( EX {nnf_term a} )

    |formula ( ~ Falsum ) -> formula ( Verum )
    |formula ( ~ Verum ) -> formula ( Falsum )

    |formula ( Falsum ) -> formula ( Falsum )
    |formula ( Verum ) -> formula ( Verum )
    
let neg_term = function formula ( a ) -> formula ( ~ a ) 
