
module Make(T: sig type t class set : [t] TwbSet.ct end) = struct
        
    type t = T.t 
    module Ft =
        struct
            type t = T.set
            let copy s = s#copy
            let to_string s = s#to_string
        end

    module Map = TwbHash.Make(Ft)

    class map pattern =
        object(self : 'a)

            val data = object
                inherit Map.map as super
                method to_string =
                    super#fold (fun k v s ->
                            let str = (Ft.to_string v) in
                            if s = "" && str = "" then ""
                            else if s = "" then Format.sprintf "%s" str
                            else Format.sprintf "%s ; %s" s str
                    ) ""
            end

            method private addel map el =
                let key = pattern el in
                let set =
                    try map#find key
                    with Not_found -> new T.set
                in
                map#add key (set#add el)

            method addlist id l =
                let newdata =
                    match id with
                    |"" ->
                            List.fold_left (fun map el ->
                                self#addel map el
                            ) (data#copy) l
                    |key ->
                            let set =
                                try data#find key
                                with Not_found -> new T.set
                            in
                            let newset = List.fold_left (
                                fun s e -> s#add e
                            ) set l
                            in (data#copy)#add key newset
                in {< data = newdata >}

            method add e = {< data = self#addel (data#copy) e >}

            method del e =
                try let key = pattern e in
                    let set = (data#find key)#del e in
                    {< data = (data#copy)#replace key set >}
                with Not_found -> {< >}

           method replace key set =
                {< data = (data#copy)#add key set >}

           method find = function
            |"" -> data#fold (fun _ v s -> s#addlist (v#elements)) (new T.set)
            |_ as key -> try data#find key with Not_found -> new T.set

            method copy = {< data = data#copy >}

            method empty = {< data = new Map.map >}

            method to_string = data#to_string
        end

end

