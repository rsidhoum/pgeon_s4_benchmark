
class type ['t,'c] ct =
  object ('a)
    method add : 't -> 'a
    method addlist : string -> 't list -> 'a
    method replace : string -> 'c -> 'a
    method find : string -> 'c
    method copy : 'a
    method del : 't -> 'a
    method empty : 'a
    method to_string : string
  end

module type S =
    sig
        type t
        class map : (t -> string) -> [t, t TwbSet.ct] ct
    end

module Make(T : sig type t type map = (t, t TwbSet.ct) ct end) = 
    struct
   
    class container init = 
        object(self)
            val data : T.map array = init
            method private arrcopy data = 
                Array.map (fun e -> e#copy) data
            method get i = data.(i)
            method set i e =
                let newdata = self#arrcopy data in
                let _ = newdata.(i) <- e in
                {< data = newdata >}
            method copy = {< data = self#arrcopy data >}
            method to_string = 
                if Array.length data = 1 then data.(0)#to_string
                else
                    Array.fold_left (fun s m ->
                        let ss = m#to_string in
                        if s = "" then (ss^" =>") else (s^" "^ss)
                    ) "" data
            method empty = {< data = init >}
        end
        
    end
