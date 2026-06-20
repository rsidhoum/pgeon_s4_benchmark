
type 'a llist = 'a cell Lazy.t
and 'a cell = LList of 'a * 'a llist | Empty

exception LListEmpty of string

let empty = lazy(Empty)
let push e l = lazy(LList(e,l))
let pop s = 
    match Lazy.force s with
    | LList (hd, tl) -> (hd,tl)
    | Empty -> raise (LListEmpty "pop")

let hd s =
    match Lazy.force s with
    | LList (hd, _) -> hd
    | Empty -> raise (LListEmpty "hd")

let tl s =
    match Lazy.force s with
    | LList (_, tl) -> tl
    | Empty -> raise (LListEmpty "tl")

let rec append s1 s2 =
    lazy begin
        match Lazy.force s1 with
        | LList (hd, tl) -> LList (hd, append tl s2)
        | Empty -> Lazy.force s2
    end

let rec flatten ss =
    lazy begin
        match Lazy.force ss with
        | Empty -> Empty
        | LList (hd, tl) ->
            match Lazy.force hd with
            | LList (hd2, tl2) -> LList (hd2, flatten (lazy (LList (tl2, tl))))
            | Empty -> Lazy.force (flatten tl)
    end

let rec map f s =
    lazy begin
        match Lazy.force s with
        | LList (hd, tl) -> LList (f hd, map f tl)
        | Empty -> Empty
    end

let rec filter_map f s =
    lazy begin
        match Lazy.force s with
        | LList (hd, tl) ->
                begin match f hd with
                |Some y -> LList (y, filter_map f tl)
                |None -> Lazy.force(filter_map f tl)
                end
        | Empty -> Empty
    end

let rec filter f s =
    lazy begin
        match Lazy.force s with
        | LList (hd, tl) ->
                begin match f hd with
                |true -> LList (hd, filter f tl)
                |false -> Lazy.force(filter f tl)
                end
        | Empty -> Empty
    end

let rec clone s =
    lazy begin
        match Lazy.force s with
        | LList (hd, tl) -> LList(hd,clone s)
        | Empty -> Empty
    end

let reverse s =
    let rec loop acc l =
        begin
            match Lazy.force l with
            | LList (hd, tl) -> loop (push hd acc) tl
            | Empty -> acc
        end
    in loop empty s

let to_list s = 
    let rec loop acc = function
        | LList (hd, tl) -> loop (hd :: acc) (Lazy.force tl)
        | Empty -> acc
    in List.rev (loop [] (Lazy.force s))

let rec of_list = function
    | [] -> lazy(Empty)
    | hd :: tl -> lazy (LList (hd, of_list tl))

let is_empty s =
    match Lazy.force s with
    |Empty -> true
    |_ -> false

let rec for_all p l = 
    match Lazy.force l with
    | Empty -> true
    | LList (hd, tl) -> p hd && for_all p tl

let rec exists p l =
    match Lazy.force l with
    | Empty -> false
    | LList (hd, tl) -> p hd || for_all p tl

type 'a excp = Nothing | Just of ('a * 'a llist)

(* XXX *)
let rec xmerge ll =
    lazy begin match Lazy.force ll with
        |Empty -> Empty 
        |LList(h,t) -> 
                let hd () =
                    let tl = filter_map (fun l ->
                        try Some(hd l) with LListEmpty _ -> None ) t
                    in if is_empty h then Lazy.force(tl) else LList(hd h,tl)
                in 
                let tl = filter_map (fun l ->
                    try Some(tl l) with LListEmpty _ -> None) ll
                in 
                Lazy.force(
                    filter_map (fun n ->
                        if is_empty n then None else Some(n)
                    ) (lazy(LList(lazy(hd ()),xmerge tl)))
                )
    end

(* monadic operators *)
type 'a m = 'a llist
let return x = push x empty
let bind l f = flatten (map f l)

let mzero = empty
let mplus = append

let guard b = if b then return () else mzero
let determ m = if is_empty m then mzero else return (hd m)

let msplit s =
    match Lazy.force s with
    |Empty -> return (Nothing)
    |LList (hd, tl) -> return (Just(hd,tl))
let ifte t th el =
    bind (msplit t) (function
        |Nothing -> el
        |Just (sg1,sg2) -> mplus (th sg1) (bind sg2 th)
    )

(*
let once m =
    bind (msplit m) (function
        |Nothing -> mzero
        |Just (sg1,_) -> return sg1
    )
*)
module type Seq =
  sig
    type 'a m
    type 'a excp = Nothing | Just of ('a * 'a m)
    val return : 'a -> 'a m
    val bind   : 'a m -> ('a -> 'b m) -> 'b m
    val mzero  : 'a m
    val mplus  : 'a m -> 'a m -> 'a m
    val guard  : bool -> unit m
    val determ : 'a m -> 'a m
    val msplit : 'a m -> 'a excp m
    val ifte   : 'a m -> ('a -> 'b m) -> 'b m -> 'b m
  end
