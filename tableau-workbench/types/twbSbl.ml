
class type ['t,'c] ct =
    object('a)
        method add : (string * 't list) list -> 'a
        method find : string -> 'c
        method is_empty : bool
        method mem : string -> 't -> bool
        method copy : 'a
        method empty : 'a
        method to_string : string
      end

module Make(T: sig type t class set : [t] TwbSet.ct end) :
    sig
        class sbl : [T.t, T.set] ct
    end
    = struct

        module Ft =
            struct
                type t = T.set
                let copy s = s#copy
                let to_string s = s#to_string
            end

        module Map = TwbHash.Make(Ft)

        exception Stop

        class sbl =
            object

                val data = new Map.map

                method add l =
                    let newdata =
                        List.fold_left (
                            fun map (k,v) ->
                                try
                                    let set = (map#find k)
                                    in map#replace k (set#addlist v)
                                with Not_found ->
                                    map#add k ((new T.set)#addlist v)
                        ) (data#copy) l
                    in {< data = newdata >}

                method find key = data#find key

                method is_empty =
                    try
                        data#fold (fun _ v b ->
                            match v,b with
                            |l,true -> l#is_empty
                            |l,false -> raise Stop
                        ) true
                    with Stop -> false

                method mem key e = (data#find key)#mem e

                method copy = {< data = data#copy >}

                method empty =
                    let newdata =
                        data#fold (fun k _ s ->
                            s#add k (new T.set)
                        ) (new Map.map)
                    in {< data = newdata >}

                method to_string = data#to_string

            end
    end

