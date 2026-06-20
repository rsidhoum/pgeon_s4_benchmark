source CtlMark

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
    type t = FormulaSet.set
    let to_string s = s#to_string
    let copy s = s#copy
  end
 )


let uevundef () = new FormulaIntSet.set


let excl uev p =
  let p = List.hd p in
  try
    let pair = List.find (fun (f, _) -> f = p) uev#elements in
    uev#del pair
  with Not_found -> uev

let doNextChild_disj (mrk, uev, p) = 
  if mrk then true
  else
    let uev = excl uev p in
    not uev#is_empty

let uev_disj (mrks, uevs, p) = 
  let takemin uev1 uev2 =
    let l1 = uev1#elements in
    let l2 = uev2#elements in
    let filter res (x, i) =
      try
        let (_, j) = List.find (fun (y, _) -> y = x) l2 in
        (x, min i j)::res
      with Not_found -> res
    in
    let lst = List.fold_left filter [] l1 in
    new FormulaIntSet.set#addlist lst
  in
  match (mrks, uevs) with
  | ([mrk1], _)  -> uevundef ()
  | ([mrk1; mrk2], _) when mrk1 && mrk2 -> uevundef ()
  | ([mrk1; mrk2], [uev1; _]) when (not mrk1) && mrk2 -> excl uev1 p
  | ([mrk1; mrk2], [_; uev2]) when mrk1 && (not mrk2) -> uev2
  | (_, [uev1; uev2]) -> takemin (excl uev1 p) uev2
  | _ -> failwith "uev_disj"

let mrk_disj mrks =
  if List.length mrks = 1 then false
  else List.nth mrks 1


let condD (ex, ax) =
  match (ex, ax) with
  | ([], h::tl) -> true
  | _ -> false


let emptycheck(ex, ax) = if ex = [] then [] else ax

let loop_check (diax, box, hcore) =
  let nodeset = (new FormulaSet.set)#addlist (diax@box) in
  not(List.exists (fun s -> nodeset#is_equal s) hcore#elements)

let push (dia, box, hcore) = 
  let nodeset = (new FormulaSet.set)#addlist (dia@box) 
  in hcore#add nodeset

let test_ext (mrk, uev, dia, box, hcore) =
  if mrk then false
  else
    let len = hcore#length in
    let uevl = uev#elements in
    let chkloop f (x, i) = (x = f) && (i >= len) in
    not (List.exists (fun f -> List.exists (chkloop f) uevl) (dia@box))

let uev_ext (mrks, uevs, diax, box) =
  if List.length mrks = 1 then uevundef()
  else
    let mrk2 = List.nth mrks 1 in
    if mrk2 then uevundef ()
    else
      let dia = List.hd diax in
      let l1 = (List.hd uevs)#elements in
      let l2 = (List.nth uevs 1)#elements in
      let filter1 res (x, i) =
        match x with
        | formula (E a U d) when x = dia -> (x, i)::res
        | formula (A a U d) when List.mem x box ->
            begin 
              try
                let (_, j) = List.find (fun (y, _) -> y = x) l2 in
                (x, max i j)::res
              with Not_found -> (x, i)::res
            end
        | _ -> res
      in
      let filter2 res (x, i) =
        match x with
        | formula (E a U d) -> (x, i)::res
        | formula (A a U d) ->
            if List.exists (fun (y, _) -> y = x) l1 then res
            else (x, i)::res
        | _ -> failwith "uev_ext"
      in
      let lst1 = List.fold_left filter1 [] l1 in
      let uev = new FormulaIntSet.set#addlist lst1 in
      let lst2 = List.fold_left filter2 [] l2 in
      uev#addlist lst2

let mrk_ext mrks = 
  if List.length mrks = 1 then true
  else List.nth mrks 1


let uev_loop (diax, box, hcore) = 
  let hcore = hcore#elements in
  let rec index nodeset hcore n = 
    match hcore with
    | [] -> failwith "index"
    | h::tl -> 
        if nodeset#is_equal h then n
        else index nodeset tl (n+1)
  in
  let getindex dia = 
    let nodeset = (new FormulaSet.set)#addlist (dia::box) in
    let i = index nodeset hcore 0 in
    (dia, i)
  in
  let fltrEU (x, _) =
    match x with
    | formula (E a U d) -> true
    | _ -> false
  in
  let fltrAU = function
    | formula (A a U d) -> true
    | _ -> false
  in
  let dialist = List.map getindex diax in
  let maxlvl = List.fold_left (fun m (_, i) -> max m i) 0 dialist in
  let eulist = List.filter fltrEU dialist in
  let aulist = List.filter fltrAU box in
  let aulist = List.map (fun x -> (x, maxlvl)) aulist in
  (new FormulaIntSet.set)#addlist (eulist@aulist)
