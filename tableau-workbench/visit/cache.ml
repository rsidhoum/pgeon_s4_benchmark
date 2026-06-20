
module type S =
sig
    type node
    class cache : bool ->
          object('cache)
              method add  : node -> node Tree.result -> unit
              method mem  : node -> bool
              method find : node -> node Tree.result
              method clear : 'cache
              method to_string : string
              method stats : string
          end
end


module Make (N:Node.S) =
  struct

        type node = N.node
        let hash n = Hashtbl.hash n#marshal
        
        module Hash = Hashtbl.Make(
            struct 
                type t = node
                let equal n1 n2 = (n1#to_string) = (n2#to_string)
                let hash = hash
            end)
        
        class cache enabled =
            object(self)
                val data : node Tree.result Hash.t = Hash.create 2879
                val enabled = enabled
                
                val mutable hits = 0
                val mutable miss = 0
                
                method mem k = 
                    if enabled then
                        if Hash.mem data k
                        then (hits <- hits +1; true)
                        else (miss <- miss +1; false)
                    else false
                
                method find k =
                    if enabled then
                        try 
                            let v = Hash.find data k in
                            (hits <- hits +1; v)
                        with Not_found -> 
                            (miss <- miss +1; raise Not_found)
                    else raise Not_found

                (* I need to force the result of the computation to
                 * avoid Lazy.Undefined *)
                method add k v = if enabled then Hash.add data k v else ()

                method to_string = ""
(*                    Hash.fold (
                        fun k v s ->
                            Printf.sprintf "%s\nkey:%s\nvalue:%s"
                            s k#to_string v#to_string
                    ) data ""
*)
                method stats = 
                    Printf.sprintf
                    "Cache results:\nTotal queries:%d\nHits:%d\nMiss:%d\nElements in the cache:%d\n"
                    (hits+miss) hits miss (Hash.length data)

                method clear = {< data = Hash.create 2879 >}
            end
    end

