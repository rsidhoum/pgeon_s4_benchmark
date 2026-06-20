
source Ctl

module FormulaSet = TwbSet.Make(
    struct
        type t = formula
        let to_string = formula_printer
        let copy s = s
    end
)

module FormulaIntSet = TwbSet.Make(
    struct
        type t = formula * int
        let to_string (f,i) = Printf.sprintf "(%i,%s)" i (formula_printer f)
        let copy s = s
    end
)

module ListFormulaSet = TwbList.Make(
    struct
        type t = (FormulaSet.set * FormulaSet.set)
        let to_string (s1,s2) =
            Printf.sprintf "(%s,%s)" s1#to_string s2#to_string
        let copy (s1,s2) = (s1#copy,s2#copy)
    end
)

let rec filter_map f = function
    | [] -> []
    | hd :: tl ->
            begin match f hd with
            |None -> filter_map f tl
            |Some(a) -> a :: filter_map f tl
            end

(* debug flag *)
let debug = ref false

let not_false uev =
    not(List.exists (function
        |formula ( Falsum ),_ -> true
        |_ -> false
    ) uev#elements)

let push (dia,box,fev,br) = 
    let nodeset = (new FormulaSet.set)#addlist (dia@box) 
    in br#add (nodeset,fev)

let termfalse = formula ( Falsum ) 
let setclose br = (new FormulaIntSet.set)#add (termfalse, br#length)

let setuev_beta (uev1, uev2, br) =
    let l = (br#length -1) in
    let _ =
        if !debug then
        Printf.printf "BETA\nm:%d\nuev1: %s\nuev2: %s\nBr: %s\n"
        l uev1#to_string uev2#to_string br#to_string
        else ()
    in 
    if (List.exists (function
        |formula ( Falsum ),_ -> true
        | _ -> false) uev2#elements) 
    then uev1

    else if (List.exists (function
        |formula ( Falsum ),_ -> true
        | _ -> false) uev1#elements) 
    then uev2
    
    else 
        let a = 
        (new FormulaIntSet.set)#addlist(
            filter_map (fun (x,nx) ->
                try
                    let (z,nz) = 
                        List.find (fun (y,_) -> y = x) uev1#elements
                    in
                    begin match x with
                    |formula (A a U d) -> Some(x,min nx nz)
                    |formula (E a U d) -> Some(x,max nx nz)
                    |_ -> failwith "dddddd"
                    end
                with Not_found -> None
            ) uev2#elements
        )
        in if !debug then (Printf.printf "INTER %s\n" a#to_string ; a) else a

let rec index n s l =
    if List.length l > 0 then
        if s#is_equal (List.nth l n) then n
        else
            if n < ((List.length l) - 1) then index (n+1) s l
            else failwith "index: core not found"
    else failwith "index: list empty"


(* true if there is not an element in the list equal to (dia@box) *)
let loop_check (dia,box,br) =
    let set = (new FormulaSet.set)#addlist (dia@box) in
    not(List.exists (fun (s,_) -> set#is_equal s) br#elements)

exception Stop_exn of int ;;
let procastinator idx ev (br1,br2) = 
    let bra1 = Array.of_list br1 in
    let bra2 = Array.of_list br2 in
    let len = Array.length bra1 in
    try
        Array.iter (fun set ->
            if (set#mem ev) then ()
            else raise ( Stop_exn 0)
        ) (Array.sub bra1 idx ( len - idx )) ;
        (* the fev are displaced by one and were happy if it is not in the fev *)
        Array.iter (fun fev ->
            if not(fev#mem ev) then ()
            else raise ( Stop_exn 0)
        ) (Array.sub bra2 (idx + 1) ( len - (idx + 1) )) ;
        true
    with Stop_exn _ -> false

let setuev_loop (diax,box,fev,brl) =
    let (br1, br2) = List.split brl#elements in
    let checkuev node fev br =
        let set = (new FormulaSet.set)#addlist node in
        if List.exists ( fun s -> set#is_equal s ) br then
            let i = index 0 set br in
            Some(
                (new FormulaIntSet.set)#addlist (
                    filter_map (function
                        |formula (E a U d) as ev when
                        procastinator i ev (br1,br2) && (* it's a procastinator *)
                        not(fev#mem ev) -> (* and is not in the fev of the last world *)
                            Some(formula (E a U d),i)
                        |formula (A a U d) as ev when
                        procastinator i ev (br1,br2) &&
                        not(fev#mem ev) -> 
                            Some(formula (A a U d),i)
                        |_ -> None
                    ) (node)
            )
            )
        else begin
            print_endline "SetUEV but not in Br !!!";
            print_endline set#to_string;
            failwith "This should never happen"
        end
    in
    let uevlist =
                filter_map(fun dia ->
                    checkuev (dia::box) fev br1
                ) diax
    in
    let uev =
        List.fold_left (fun e s -> s#union e)
        (new FormulaIntSet.set) uevlist
    in
    if !debug then Printf.printf "SetUevLoop: %s\n" (uev#to_string)
    else () ;
    uev

let setuev_pi (uev1, uev2, br) = 
    let l = (br#length -1) in
    let uev = (uev1#union uev2) in
    let _ =
        if !debug then
        Printf.printf "PI\nm:%d\nuev: %s\n" l uev#to_string
        else ()
    in
    if List.exists ( fun (_,n) -> n > l ) uev#elements
    then (new FormulaIntSet.set)#add (termfalse,l+1)
    else if List.exists (function
        |formula ( Falsum ),_ -> true
        |_ -> false
        ) uev#elements
    then (new FormulaIntSet.set)#add (termfalse,l+1)
    else if List.for_all ( fun (_,n) -> n <= l ) uev#elements
    then uev
    else failwith ("pi: impossible")
