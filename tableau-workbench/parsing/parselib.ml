(*pp camlp5o -I . pa_extend.cmo q_MLast.cmo *)

let loc = Stdpp.dummy_loc

module Options =
    struct
        let debug = ref false
        let cgi   = ref false
        let print s = if !debug then Printf.eprintf "%s" s else ()
    end
;;

Pcaml.add_option "--debug"  (Arg.Set Options.debug) "Enable Pre-Processor debug";;
Pcaml.add_option "--cgi"    (Arg.Set Options.cgi  ) "Compile Cgi support" ;;

let rec unique = function
    |[] -> []
    |h::t -> h:: unique (List.filter (fun x -> not(x = h)) t)

let filter_map f l =
    let rec aux acc f = function
        |[] -> acc
        |h::t ->
                begin match f h with
                |None -> aux acc f t
                |Some(x) -> aux (x::acc) f t
                end
    in aux [] f l

let vala value = Ploc.VaVal value

let unvala = function
    |Ploc.VaVal value -> value
    |Ploc.VaAnt _ -> assert(false)

let list_to_exprlist l =
    List.fold_right (
        fun x l -> <:expr< [ $x$ :: $l$ ] >>
    ) l <:expr< [] >>

let list_to_pattlist l =
    List.fold_right (
        fun x l -> <:patt< [ $x$ :: $l$ ] >>
    ) l <:patt< [] >>

let pa_expr_is_var = function
    |Ast.PaTerm(Ast.PaVar(_)) -> true
    |Ast.PaLabt(_,Ast.PaVar(_)) -> true
    |_ -> false

let new_id =
  let counter = ref 0 in
  fun s ->
      incr counter;
      "__" ^s^ string_of_int !counter

let new_co =
  let counter = ref 0 in
  fun s ->
      incr counter;
      s ^ string_of_int !counter

(* FIXME: to be moved *)
module Option = struct
    let get = function Some x -> x | None -> assert(false)
    let optlist = function Some l -> l | None -> []
    let optarray = function Some l -> l | None -> [||]
    let is_none = function Some _ -> false | None -> true
end
