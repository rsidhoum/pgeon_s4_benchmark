
class type ['t] ct =
    object('a)
        method add : 't -> 'a
        method add_filter : ('t -> 't -> bool ) -> 't -> 'a
        method addlist : 't list -> 'a
        method del : 't -> 'a
        method mem : 't -> bool
        method elements : 't list
        method hd : 't
        method is_empty : bool
        method filter : ('t -> bool) -> 'a
        method length : int
        method cardinal : int
        method intersect : 'a -> 'a
        method union: 'a -> 'a
        method subset: 'a -> bool
        method is_equal : 'a -> bool
        method copy : 'a
        method empty : 'a
        method to_string : string
    end

module type ValType =
    sig
        type t
        val copy : t -> t
        val to_string : t -> string
    end

module Make (T : ValType) : sig class set : [T.t] ct end = struct

    module Set = Set.Make (struct type t = T.t let compare = compare end)

    let copy s = Set.fold (fun v s' -> Set.add (T.copy v) s') s Set.empty

    class set =
        object(self : 'a)
            val data = Set.empty
            val mutable modified = true
            val mutable to_string_cache = ""
            
            (* XXX: insertion is o(log n) *)
            method add e = {< 
                modified = true;
                to_string_cache = "";
                data = Set.add e data
            >}

            (* XXX: insertion is o(n * log n) *)
            method add_filter f e = {<
                modified = true;
                to_string_cache = "";
                data =
                    let s' = Set.filter (fun el -> f e el) data in
                    Set.add e s'
            >}
            
            method addlist l = {< 
                modified = true;
                to_string_cache = "";
                data = List.fold_left (fun s e -> Set.add e s ) data l 
            >}

            (* XXX: deletions is o(log n) *)
            method del e = {<
                modified = true;
                to_string_cache = "";
                data = Set.remove e data
            >}
            
            (* XXX: copy is o(n) *)
            method copy = {< data = (copy data) >}

            method empty = {<
                modified = true;
                to_string_cache = "";
                data = Set.empty 
            >}

            method mem e = Set.mem e data 

            method filter f = {<
                modified = true;
                to_string_cache = "";
                data = Set.filter f data 
            >}

            method elements = Set.elements data

            method hd = Set.min_elt data

            method is_empty = Set.is_empty data

            method cardinal = Set.cardinal data
            method length = self#cardinal

            (* here I create a set and the use inter.
             * XXX: I'm double minded ...
             * the other ways is to expose a method to access the
             * interal represenation of the set, but this will
             * break the data incapsulation ... Friends functions ?? *)
            method intersect (set : 'a) = {<
                modified = true;
                to_string_cache = "";
                data =
                    Set.inter data
                    (List.fold_left
                        (fun e s -> Set.add s e)
                        Set.empty set#elements
                    )
            >}

            method subset (set :'a) =
                Set.subset data 
                    (List.fold_left
                        (fun e s -> Set.add s e)
                        Set.empty set#elements
                    )

            method union (set : 'a) = {<
                modified = true;
                to_string_cache = "";
                data =
                    Set.union data
                    (List.fold_left
                        (fun e s -> Set.add s e)
                        Set.empty set#elements
                    )
            >}
                    
            method is_equal (set : 'a) =
                Set.equal
                data 
                (List.fold_left
                    (fun e s -> Set.add s e)
                    Set.empty set#elements
                )
           
            (* since we use to_string to index the set in a hash table,
             * I want to minimize the number of times I exectute this
             * function. *) 
            method to_string =
                if modified then begin
                    let s = Set.fold (
                        fun e s ->
                            if s = "" then Format.sprintf "%s" (T.to_string e)
                            else Format.sprintf "%s ; %s" s (T.to_string e)
                        ) data ""
                    in
                    modified <- false;
                    to_string_cache <- s;
                    to_string_cache
                end else to_string_cache 
        end
end
