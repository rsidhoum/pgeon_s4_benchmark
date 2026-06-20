let find_index predicate values =
  let rec loop index = function
    | [] -> None
    | value :: rest ->
        if predicate value then Some index else loop (index + 1) rest
  in
  loop 0 values

let seq_mapi f values =
  let rec loop index values () =
    match values () with
    | Seq.Nil -> Seq.Nil
    | Seq.Cons (value, rest) ->
        Seq.Cons (f index value, loop (index + 1) rest)
  in
  loop 0 values

let seq_uncons values =
  match values () with Seq.Nil -> None | Seq.Cons (value, rest) -> Some (value, rest)

let rec seq_interleave left right () =
  match left () with
  | Seq.Nil -> right ()
  | Seq.Cons (value, rest) ->
      Seq.Cons (value, seq_interleave right rest)

let rec seq_exists predicate values =
  match values () with
  | Seq.Nil -> false
  | Seq.Cons (value, rest) ->
      predicate value || seq_exists predicate rest
