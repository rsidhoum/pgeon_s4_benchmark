
module type S =
    sig
        type t 
        type sbl = private < copy : 'a ; empty : 'a ; is_empty : bool ; .. > as 'a
        type hist
        type var
        type container = private < 
            copy : 'a ; 
            get : int -> (t,t TwbSet.ct) TwbContainer.ct ;
            set : int -> (t,t TwbSet.ct) TwbContainer.ct -> 'a ; ..> as 'a 
        type pattern = { pcid : int ; pid : string ; pmatch : sbl -> t list -> (t list * sbl) }
        type action  = { acid : int ; aid : string ; paction : sbl -> hist -> var list -> t list }
    end

module type ValType =
    sig
        type t
        type sbl
        type hist
        type var
        type container
    end
    
module Make (T : ValType) =
    struct
        type t = T.t
        type sbl = T.sbl
        type hist = T.hist
        type var = T.var
        type container = T.container
        type pattern = { pcid : int ; pid : string ; pmatch : sbl -> t list -> (t list * sbl) }
        type action  = { acid : int ; aid : string ; paction : sbl -> hist -> var list -> t list }
        let newpatt n id pmatch = { pcid = n ; pid = id ; pmatch = pmatch }
        let newact n id paction = { acid = n ; aid = id ; paction = paction }
    end
