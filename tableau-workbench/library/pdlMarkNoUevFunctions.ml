source PdlMarkNoUev

module FormulaSet = TwbSet.Make(
  struct
    type t = formula
    let to_string = formula_printer
    let copy s = s
  end
 )

module FormulaIntSet = TwbSet.Make(
  struct
    type t = ( formula * int )
    let to_string (f,i) =
      Printf.sprintf "(%i,%s)" i (formula_printer f)
    let copy s = s
  end
 )

module ListFormulaSet = TwbList.Make(
  struct
    type t = ( formula * FormulaSet.set )
    let to_string (f,s) = Printf.sprintf "(%s,%s)" (formula_printer f) s#to_string
    let copy (f,s) = (f, s#copy)
  end
 )

class nextFormula =
  object
    val f : formula option = None
    method get = f
    method set nf = {< f = nf >}
    method copy = {< >}
    method to_string = 
      match f with
      | None -> "Undefined"
      | Some f -> formula_printer f
  end

class depth =
  object
    val i : int = 0
    method get = i
    method set ni = {< i = ni >}
    method incr () = {< i = succ i >}
    method copy = {< >}
    method to_string = string_of_int i
  end


let undef_HNx hnx =
  match hnx#get with
  | None -> true
  | _ -> false


let notinHB(p, hbb) = not (hbb#mem (List.hd p))

let pushHBB(p, hbb) = hbb#add (List.hd p)

let inHB(p, hbb) = hbb#mem (List.hd p)


let undefOrP_HNx (hnx, p) =
  match hnx#get with
  | None -> true
  | Some f -> f = List.hd p


let rec isFean = function
  | formula ( < * a > p ) -> true
  | formula ( < a U b > p ) -> true
  | formula ( < a ; b > p ) -> true
  | formula ( < ? f > p ) -> true
  | _ -> false

let testchain_HNx f =
  let f = List.hd f in
  if isFean f then (new nextFormula)#set (Some f)
  else new nextFormula
  
let testchain_HBD (f, hbd) =
  if isFean (List.hd f) then hbd else new FormulaSet.set

let testchain_HBD_Star (f, hbd, pf) =
  if isFean (List.hd f) then hbd#add (List.hd pf)
  else new FormulaSet.set


let isDia = function
  | formula ( < _ > _ ) -> true
  | _ -> false

let tstHfoc (pf, f1, hfoc) =
  match hfoc#get with
  | None -> hfoc
  | Some f -> 
      let pf = List.hd pf in
      if f = pf then
        let f1 = List.hd f1 in
        if isDia f1 then hfoc#set (Some f1)
        else new nextFormula
      else hfoc

let setHfoc (pf, f1, hfoc) =
  match hfoc#get with
  | None -> hfoc
  | Some f -> 
      let pf = List.hd pf in
      if f = pf then 
        let f1 = List.hd f1 in
        hfoc#set (Some f1)
      else hfoc


let is_true b = b

let setmrk_beta mrks =
  if List.length mrks = 1 then false
  else List.nth mrks 1


let loop_check (diax, box, hcore) =
  let dia = List.hd diax in
  let nodeset = (new FormulaSet.set)#addlist (dia::box) in
  not(List.exists (fun (f, s) -> f = dia && nodeset#is_equal s) hcore#elements)

let push (diax, box, hcore) = 
  let nodeset = (new FormulaSet.set)#addlist (diax@box) 
  in hcore#add (List.hd diax, nodeset)

let emptyset h = h#empty

let setHfocState f =
  let f = List.hd f in
  if isDia f then (new nextFormula)#set (Some f)
  else new nextFormula

let rec lookfor f = function
  | [] -> None
  | (f1, i1)::t -> 
      if f = f1 then Some i1
      else lookfor f t

let newHchn (pf, f1, hfoc, hchn, dpt) =
  let pf = List.hd pf in
  let f1 = List.hd f1 in
  if isDia f1 then
    match hfoc#get with
    | None -> (new FormulaIntSet.set)#add (f1, dpt#get)
    | Some f ->
        begin
          if pf = f then 
            let hchnl = hchn#elements in
            match lookfor f1 hchnl with
            | None -> hchn#add (f1, dpt#get)
            | Some _ -> hchn
          else (new FormulaIntSet.set)#add (f1, dpt#get)
        end
  else new FormulaIntSet.set

let increaseDpt dpt = dpt#incr ()

let is_false b = not b

let setmrk_ext mrks =
  if List.length mrks = 1 then true
  else List.nth mrks 1


let setmrk_loop(diax, box, hcr, hfoc, hchn, dpt) =
  let hcr = hcr#elements in
  let hchnl = hchn#elements in
  let filterbox a res = function
    | formula ( [ x ] p ) when x = a -> p::res
    | _ -> res
  in
  let rec index p nodeset hcore n = 
    match hcore with
    | [] -> failwith "setmrk_loop: index"
    | (f, s)::tl -> 
        if f = p && nodeset#is_equal s then n
        else index p nodeset tl (n+1)
  in
  let getindex = function
    | formula ( < a >  p ) ->
        let boxa = List.fold_left (filterbox a) [] box in
        let nodeset = (new FormulaSet.set)#addlist (p::boxa) in
        let i = index p nodeset hcr 0 in
        (p, i)
    | _ ->  failwith "setmrk_loop: getindex"
  in
  let checkdia res dia =
    if res then true
    else
      let (f1, i) = getindex dia in
      if isDia f1 then
        match hfoc#get with
        | None -> false
        | Some f ->
            begin
              if dia = f then 
                match lookfor f1 hchnl with
                | None -> false
                | Some n -> n <= i
              else false
            end
      else false
  in
  List.fold_left checkdia false diax
