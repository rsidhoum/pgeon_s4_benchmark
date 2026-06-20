type formula = int * Term.t (* id, term *)

type proof_tree =
  formula list list (* list of branches, each branch is a list of terms *)

let is_closed = function [] -> true | _ -> false

type application_key = int * Term.t list * Term.t list

type proof_state = {
  tree : proof_tree;
  next_fresh : int;
  next_symbol : int;
  next_formula_id : int;
  applied : application_key list; (* applied rules and structural principals *)
}

type strategy = proof_state -> proof_state Seq.t

type rule = {
  id : int;
  run : proof_state -> proof_state Seq.t;
  run_bang : strategy option;
}

let fair_flat_map f xs = xs |> Seq.map f |> Utils.diagonal

(* combinators *)
let skip = fun st -> Seq.return st
let fail = fun _ -> Seq.empty

(* let orElse s1 s2 = fun st -> Seq.append (s1 st) (s2 st) *)
let orElse s1 s2 =
 fun st ->
  let xs = s1 st in
  match xs () with Seq.Nil -> s2 st | Seq.Cons (x, rest) -> Seq.cons x rest

let andThen s1 s2 = fun st -> Seq.flat_map s2 (s1 st)
let orAlt s1 s2 = fun st -> Compat.seq_interleave (s1 st) (s2 st)
let andAlt s1 s2 = fun st -> fair_flat_map s2 (s1 st)
let rec repeat s st () = Seq.Cons (st, fair_flat_map (repeat s) (s st))

let optional s st =
  let results = s st in
  match results () with
  | Seq.Nil -> Seq.return st
  | Seq.Cons (st', rest) -> Seq.cons st' rest

let applyRule r = fun st -> r.run st

let applyRuleBang r =
 fun st ->
  match r.run_bang with
  | None -> failwith "Rule does not support bang application"
  | Some f -> f st

(* main engine *)
let prove st s = Compat.seq_exists (fun st -> is_closed st.tree) (s st)
