
class type ['t] ct =
  object ('a)
    method add : string -> 't -> 'a
    method replace : string -> 't -> 'a
    method find : string -> 't
    method fold : 'd . (string -> 't -> 'd -> 'd) -> 'd -> 'd
    method mem : string -> bool
    method copy : 'a
    method empty : 'a
    method to_string : string
  end

module Make(T: TwbSet.ValType) : sig class map : [T.t] ct end = struct
    
    let copy h =
        Hashtbl.fold (fun k v tbl ->
            Hashtbl.add tbl k (T.copy v) ; tbl
        ) h (Hashtbl.create (Hashtbl.length h))
     
    class map =
        object(self : T.t #ct)

            val data = Hashtbl.create 7
            
            method add key e =
                let h = copy data in
                let _ = Hashtbl.replace h key e in
                {< data = h >}
                
            method replace key e = self#add key e
            method find key = Hashtbl.find data key 
            method fold f s = Hashtbl.fold f data s
            method mem key = Hashtbl.mem data key
            method copy = {< data = copy data >}
            method empty = {< data = Hashtbl.create 7 >}
            method to_string =
                Hashtbl.fold ( fun k v s ->
                        let str = (T.to_string v) in
                        if str = "" then s
                        else Printf.sprintf "%s\n%s:%s" s k str
                ) data ""

 
        end
end
