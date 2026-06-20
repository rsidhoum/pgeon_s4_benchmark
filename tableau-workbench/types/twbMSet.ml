
module Make (T : TwbSet.ValType) : sig class set : [T.t] TwbSet.ct end =
    struct
        module L = TwbList.Make(T)
        class set = object
            inherit L.olist as super

            method to_string =
                List.fold_left (
                    fun s e ->
                        if s = "" then Format.sprintf "%s" (T.to_string e)
                        else Format.sprintf "%s ; %s" s (T.to_string e)
                    ) "" (super#elements)
        end
    end
