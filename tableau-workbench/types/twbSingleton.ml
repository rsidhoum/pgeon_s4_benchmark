
module Make(T: TwbSet.ValType) = struct

        type t = T.t
        module Set = TwbSet.Make(T)

        class map (_ : (T.t -> string)) =
            object(self)

                val data = new Set.set

                method addlist ( _ : string ) = function
                    |[] -> {<>}
                    |[h] -> self#add h
                    |_ -> failwith "Not possible to add more then one element at the time in a Singletong object"
                method add e = 
                            if data#length >= 1 then
                            begin
                                print_endline "Warning: You are trying to add more then one element to a Singleton object" ;
                                {< data = (new Set.set)#add e >}
                            end
                            else {< data = (new Set.set)#add e >}
                method del (_ : T.t) = {< data = new Set.set >}
                method replace (_ : string) (set : Set.set) = {< data = set >}
                method find (_ : string) = data
                method copy = {< data = data#copy >}
                method empty = {< data = new Set.set >}
                method to_string = data#to_string
            end

    end

