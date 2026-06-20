
source Bint

(* Method for constructing sets of formulae inside the TWB *)

module FormulaSet = TwbSet.Make(
    struct
        type t = formula
        let to_string = formula_printer
        let copy s = s
    end
)

(* Method for constructing sets of sets of formulae inside the TWB *)

module FormulaSetSet = TwbSet.Make(
    struct
        type t = FormulaSet.set
        let to_string s = s#to_string
        let copy s = s#copy
    end
)

(* Function conjoin gamma conjoins all the members of set gamma into
   one and-formula. 
*)

let rec conjoin = function
    | [a]  -> a
    | h::t -> formula ( h ^^ {conjoin t} )
    | _ -> assert(false)

(* Function disjoin gamma disjoins all the members of set gamma into
   one or-formula.
*)

let rec disjoin = function
    | [a]   -> a
    | h::t -> formula ( h ++ {(disjoin t)} )
    | _ -> assert(false)

(* Function bigand ss where ss is a set of sets of formulae forms
   the disjunction of each member (set of formulae) of ss, and then 
   forms the bigand of these disjunctions.
*)

let bigand = function
    |[] -> []
    |ll -> [conjoin (List.map (fun s -> disjoin s#elements) ll)]

(* Function bigor ss where ss is a set of sets of formulae forms
   the conjunction of each member (set of formulae) of ss, and then 
   forms the bigor of these conjunctions.
*)

let bigor l = 
    print_endline "bigor";
    match l with
    |[] -> []
    |ll -> [disjoin (List.map (fun s -> conjoin s#elements) ll)]


(* Function undisjoin undoes the disjoin operation.  *)

let rec undisjoin = function
    |[formula ( b ++ c )] -> b :: (undisjoin [c])
    |[formula ( c )] -> [c]
    |_ -> assert(false)

(* Function unconjoin undoes the conjoin operation.  *)

let rec unconjoin = function
    |[formula ( b ^^ c )] -> b :: (unconjoin [c])
    |[formula ( c )] -> [c]
    |_ -> assert(false)

(* Function setset d where d is a list of formulae constructs an 
   initially empty set of formulae s, adds the formulae from d to s
   and then turns s into a set of sets ss.
*)

let setset d =
    let ss = new FormulaSetSet.set in
    let s = (new FormulaSet.set)#addlist d in
    ss#add s

(* Function emptyset constructs an empty set of sets of formulae.
*)

let emptysetset () = new FormulaSetSet.set 

(* Function notin a s
   just checks if a is in s
*)

let notin(a,b) =
    match a with
    | [] -> true
    | [x] -> not(List.mem x b)
    | _ -> assert(false)


(* Function conjnotin a b d g 
   checks that a is not in d AND b is not in g.
*)

let conjnotin(a,b,d,g) = 
    not(List.mem (List.hd a) d) &&
    not(List.mem (List.hd b) g)

(* Function disjnotin a b d g 
   checks that a is not in d OR b is not in g.
*)

let disjnotin(a,b,d,g) =
    not(List.mem (List.hd a) d) ||
    not(List.mem (List.hd b) g)

(* Function rec allsubsnotinsub ps ab d
   returns false if some member of ps is in (ab union d)
           true  otherwise.
*)

let rec allsubsnotsub (ps,ab,d) =
    match ps with
      []   -> failwith "Error: allsubsnotsub called with empty PS"
    | [h]  -> not(h#subset ((new FormulaSet.set)#addlist (ab@d))) 
    | h::t -> 
            if h#subset ((new FormulaSet.set)#addlist (ab@d)) 
            then false else (allsubsnotsub (t,ab,d))

let rec compute (vars,ab,d) =
   match vars with
    |[ ]  ->  setset( ab@d )
    |h::_ when h#is_empty -> h
    |h::t -> if (h#hd)#elements = [formula ( Special )]
             then compute(t, ab, d) else h

let rec special (vars,ab,d) =
    match vars with
    |p1::_ when p1#is_empty -> p1
    |[p1;p2] -> p2
    |[p1] -> setset ([formula ( Special )])
    |_ ->  assert (false)

let parentisspecial (s,p) =
    (s#hd)#elements = [formula ( Special )] && 
    (p#hd)#elements = [formula ( Special )]

let union (x,y) = x#union y ;;

let isnotemptyandallsubsnotsub (p,ab,d) =
    not(p#is_empty) && allsubsnotsub (p#elements,ab,d) 

