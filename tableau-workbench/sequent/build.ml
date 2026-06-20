
module type S =
    sig
    type container 
    type sbl 
    type hist
    type at (* node pattern type *)
    val build_node : container -> sbl -> hist -> hist -> at -> container
    end

module Make(P: NodePattern.S) =
    struct
    
    type container = P.container
    type sbl = P.sbl
    type hist = P.hist
    type at = P.action list
    
    let build_node container sbl hist var actionlist =
                    List.fold_left (fun c a ->
                        let m  = c#get a.P.acid in
                        let m' = m#addlist a.P.aid (a.P.paction sbl hist var) in
                        c#set a.P.acid m'
                    ) container actionlist
    
    end
