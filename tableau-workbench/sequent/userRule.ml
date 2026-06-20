

module Make(MapCont : sig type t class set : [t] TwbSet.ct end)
           (SblCont : sig type t class set : [t] TwbSet.ct end)
           (H : TwbSet.ValType) (V : TwbSet.ValType) = struct

    module DataType = DataType.Make(MapCont)(SblCont)(H)(V)
    open DataType
    open Llist
    open Tree
    open Data

    let newcontext   = RuleContext.newcontext
    let build_node   = Build.build_node
    let build_sbl () = new Substitution.sbl

    let rec branchcond ?(implicit=false) context acctl tLl bll =
        let treelist = 
            try (Llist.hd tLl)::acctl
            with Llist.LListEmpty _ -> acctl
        in
        let checknext cxt tl = function
            |[] -> true
            |bl -> 
                let (_, sbl, node) = context#get in
                let (_, hist, _) = node#get in
                let varlist = 
                    List.map ( function
                        |Node(n) -> let (_,_,v) = n#get in v 
                        |_ -> assert(false)
                    ) (List.rev tl)
                    (* I've to revert the list as this is the result of
                     * the accumulator acctl plus the last explored branch *)
                in
                List.for_all ( fun f -> f sbl hist varlist ) bl
        in
        (* we have to check tLl to take into account implicit backtracking. 
         * Llist.tl forces the computation of the next node. if the branch 
         * condition fails, the next node is not explored *)
        match bll,Lazy.force(tLl) with
        (* if it's empty there is nothing to do *)
        |_,Empty -> List.rev treelist
        (* if there are no conditions, the rule cannot be implicit.
         * Since is cannot be empty, we explore the next branch. *)
        |[],_ when implicit = false ->
                branchcond ~implicit:false context treelist (Llist.tl tLl) []
        (* if it is implicit, then it can have only one condition. If the
         * condition holds, then we explore the next branch MAINTAINIG the same
         * condition *)
        |hd::[],_ when implicit = true && (checknext context treelist hd) ->
                 branchcond ~implicit:true context treelist (Llist.tl tLl) bll
        (* there is no condition on this branch, but maybe on others. We explore
         * the next branch without further checks and we pass the rest of the
         * condition list *)
        |[]::btl,_ when implicit = false ->
                branchcond ~implicit:false context treelist (Llist.tl tLl) btl
        (* if the condition is true then we explore the next branch passing the rest
         * of the condition list *)
        |hd::btl,_ when implicit = false && (checknext context treelist hd) ->
                branchcond ~implicit:false context treelist (Llist.tl tLl) btl
        |_ -> List.rev treelist 

    (* check method for any rule *)
    let check name node patternl historyl =
        OutputBroker.print_check name node ;
        let match_all node (plzero, plone, sl) hl =
            let (map, hist, varhist) = node#get in
            (* principal formulae and sets enumeration *)
            let enum =
                match plzero,plone with
                |[],[] -> Partition.match_node_set (build_sbl (),map) sl
                |[],pl1 -> Partition.match_node_one (build_sbl (),map) (pl1,sl)
                |pl0,[] -> Partition.match_node_zero (build_sbl (),map) (pl0,sl)
                |pl0,pl1 -> Partition.match_node_trail (build_sbl (),map) (pl0,pl1,sl)
            in
            let (enum, sbl, newmap) =
                let rec check_hist e =
                    let filtered_enum_cond =
                        Enum.filter (function (sbl,ns) ->
                            not(sbl#is_empty) &&
                            List.for_all (fun cond ->
                                cond sbl hist [varhist] ) hl
                        ) e
                    in
                    (* now filtered_enum contains only the enum that
                     * respect the side conditions and I can build with
                     * it the new context for the rule *)
                    try begin
                        match Enum.get filtered_enum_cond with
                        |Some (sbl, ns) -> (filtered_enum_cond, sbl, ns)
                        |None -> raise Partition.FailedMatch (* no more choices *)
                    end with Partition.FailedMatch ->
                        (Enum.empty (), build_sbl (), map)
               in check_hist enum
           in
           let newnode = node#set (newmap, hist, varhist) in
           newcontext (enum, sbl, newnode)
        in match_all node patternl historyl

    (* down method for a rule with explicit branching *)
    let down_explicit name context makelist =
      (* this is the rule application identifier *)
      let ruleid = !OutputBroker.rulecounter in
      let action_all node sbl oldvar al hl =
        let (cont, hist, varhist) = node#get in
        let newcont = build_node cont sbl hist oldvar al in
        let newhist =
            List.fold_left (fun h f ->
                let (k,v) = f sbl h oldvar in
                h#add k v
            ) hist hl
        in
        let newnode = node#set (newcont, newhist, varhist) in
        let _ = OutputBroker.print_down name sbl newnode ruleid in newnode
      in
      let rec make_llist sbl oldvar = function
          |[] -> Llist.empty
          | (node, al, hl) :: t ->
                  Llist.bind
                  (Llist.return (lazy(action_all node sbl oldvar al hl))) (fun next ->
                      let (_, _, nextvar) = (Lazy.force(next))#get in
                      Llist.push (Lazy.force(next)) (make_llist sbl (nextvar::oldvar) t)
                  )
      in
      let (_, sbl, newnode) = context#get in
      Tree (make_llist sbl [Variable.make ()] (makelist newnode))

    (* down method for a rule with implicit branching *)
    let down_implicit name context actionl historyl =
      (* this is the rule application identifier *)
      let ruleid = !OutputBroker.rulecounter in
      let action_all node sbl oldvar al hl =
        let (map, hist, varhist) = node#get in
        let newmap = build_node map sbl hist oldvar al in
        let newhist =
            List.fold_left (fun h f ->
                let (k,v) = f sbl h oldvar in
                h#add k v
            ) hist hl
        in
        let newnode = node#set (newmap, newhist, varhist) in
        let _ = OutputBroker.print_down name sbl newnode ruleid in newnode
      in
      let rec make_llist oldvar l =
          match Lazy.force l with
          |Empty -> Llist.empty
          |LList ((node, sbl, al, hl), t) ->
                  Llist.bind
                  (Llist.return (lazy(action_all node sbl oldvar al hl))) (fun next ->
                      let (_, _,nextvar) = (Lazy.force(next))#get in
                      Llist.push (Lazy.force(next)) (make_llist (nextvar::oldvar) t)
                  )
      in
      (* here we dynamically (lazily) generate the tail of the action list *)
      let rec next context =
        let (enum, sbl, node) = context#get in
        let (map, hist, vars) = node#get in
        let (newsbl, newmap) =
          (* enum is carefully constructed to take side conditions into account.
           * Since it is a lazy data structure, the conditions are computed only
           * when needed. Enum.get force the computation *)
          match Enum.get enum with
          |Some (sbl, ns) -> (sbl, ns)
          |None -> (build_sbl (), map)
        in
        if newsbl#is_empty then
            Llist.return (node, sbl, actionl, historyl)
        else
            let newnode = node#set (map, hist, vars) in
            Llist.push
            (node, sbl, actionl, historyl)
            (next (context#set (enum, newsbl, newnode)))
      in
      Tree (make_llist [Variable.make ()] (next context))

    let down_axiom name context arglist =
        let status = List.hd arglist in
        let (enum,sbl,newnode) = context#get in
        let (m, h, varhist) = newnode#get in
        let newnode = newnode#set(m#empty, h#empty, status varhist) in
        let _ = OutputBroker.print_down name sbl newnode !OutputBroker.rulecounter in 
        Leaf(newnode)

    let unbox_result = function
        |Node (n) -> n
        |_ -> assert(false)

    let status node =
        let (_, _, varhist) = (unbox_result node)#get in
        try varhist#find "status"
        with Not_found -> assert(false)

    (* up method - simple. explore the first branch, if the
     * branch condition is true, then explore the second branch. 
     * On backtrack apply a synth action. *)
    let up_explore_aux ?(implicit=false) name context treelist synthlist branchll =
        let (_, sbl, node) = context#get in
        let (_, hist, _) = node#get in
        (* tl holds the results of all branches that have been explored *)
        (* since the list is lazy, the computation is triggered here *)
        let tl = (branchcond ~implicit:implicit context [] treelist branchll) in
        let t = match List.rev tl with
            |[] -> assert(false)
            |h::_ -> h
        in
        let varlist = 
            List.map ( function
                |Node(n) -> let (_,_,v) = n#get in v 
                |_ -> assert(false)
            ) tl
        in
        let newnode =
            List.fold_left (
                fun n f ->
                    (* the function f returns the variable
                     * history (sythethized histories) *)
                    let (k,v) = f sbl hist varlist in
                    let (m,h,var) = n#get in
                    n#set (m,h,var#add k v)
            ) (unbox_result t) synthlist
        in
        let _ = OutputBroker.print_up name newnode in
        Node(newnode)

    let up_explore_implicit name context treelist synthlist branchll =
        up_explore_aux ~implicit:true name context treelist synthlist branchll
    let up_explore_simple name context treelist synthlist branchll =
        up_explore_aux ~implicit:false name context treelist synthlist branchll

    let up_explore_linear name context treelist synthlist =
        let (_, sbl, node) = context#get in
        let (_, hist, _) = node#get in
        let tl = (Llist.to_list treelist) in
        let t = match tl with
            |[] -> assert(false)
            |h::_ -> h
        in
        let varhist =
            let n = unbox_result t in
            let (_,_,v) = n#get in v
        in
        let newnode =
            List.fold_left (
                fun n f ->
                    let (k,v) = f sbl hist [varhist] in
                    let (m,h,var) = n#get in
                    n#set (m,h,var#add k v)
            ) (unbox_result t) synthlist
        in 
        let _ = OutputBroker.print_up name newnode in
        Node (newnode)

    module ExtList = struct

        exception Different_list_size of string
        let map = List.map
        let map1 = List.map
        let bind m f = List.flatten (List.map f m)
        let return x = [x]

        let combine2 f (l1,l2) =
            bind l1 (fun e1 ->
                bind l2 (fun e2 ->
                    return (f (e1,e2))
                )
            )

        let combine3 f (l1,l2,l3) =
            bind l1 (fun e1 ->
                bind l2 (fun e2 ->
                    bind l3 (fun e3 ->
                        return (f (e1,e2,e3))
                    )
                )
            )

        let combine4 f (l1,l2,l3,l4) =
            bind l1 (fun e1 ->
                bind l2 (fun e2 ->
                    bind l3 (fun e3 ->
                        bind l4 (fun e4 ->
                            return (f (e1,e2,e3,e4))
                        )
                    )
                )
            )

        let combine5 f (l1,l2,l3,l4,l5) =
            bind l1 (fun e1 ->
                bind l2 (fun e2 ->
                    bind l3 (fun e3 ->
                        bind l4 (fun e4 ->
                            bind l5 (fun e5 ->
                                return (f (e1,e2,e3,e4,e5))
                            )
                        )
                    )
                )
            )

        let rec zip2 = function
            |(h1::t1,h2::t2) -> (h1,h2)::(zip2 (t1,t2))
            |([],[]) -> []
            |_ -> failwith "Different_list_size (zip 2)"

        let rec zip3 = function
            |(h1::t1,h2::t2,h3::t3) ->
                    (h1,h2,h3)::(zip3 (t1,t2,t3))
            |([],[],[]) -> []
            |_ -> failwith "Different_list_size (zip 3)"

        let rec zip4 = function
            |(h1::t1,h2::t2,h3::t3,h4::t4) ->
                    (h1,h2,h3,h4)::(zip4 (t1,t2,t3,t4))
            |([],[],[],[]) -> []
            |_ -> failwith "Different_list_size (zip 4)"

        let rec zip5 = function
            |(h1::t1,h2::t2,h3::t3,h4::t4,h5::t5) ->
                    (h1,h2,h3,h4,h5)::(zip5 (t1,t2,t3,t4,t5))
            |([],[],[],[],[]) -> []
            |_ -> failwith "Different_list_size (zip 5)"

        let check f1 f2 ll = 
            let lenl = List.map List.length ll in
            if List.exists (fun len -> len = 0 ) lenl then [] else
            if List.exists (fun len -> not(len = List.hd lenl)) lenl
            then f1 ()
            else f2 ()

        let map2 f ((l1,l2) as l) =
            check (fun () -> combine2 f l) (fun () -> List.map f (zip2 l)) [l1;l2]

        let map3 f ((l1,l2,l3) as l) =
            check (fun () -> combine3 f l) (fun () -> List.map f (zip3 l)) [l1;l2;l3]

        let map4 f ((l1,l2,l3,l4) as l) =
            check (fun () -> combine4 f l) (fun () -> List.map f (zip4 l)) [l1;l2;l3;l4]

        let map5 f ((l1,l2,l3,l4,l5) as l) =
            check (fun () -> combine5 f l) (fun () -> List.map f (zip5 l)) [l1;l2;l3;l4;l5]

        let fold f fl sl =
            let rec def acc = function
                |0 -> acc
                |i -> def ([]::acc) (i-1)
            in
            let rec aux f (matched,acc) = function
                |h::tl ->
                        begin match f h with
                        |[] -> aux f (matched,acc) tl
                        |rl -> aux f (h::matched,(List.map2 (fun e l -> e::l) rl acc)) tl end
                |[] -> (matched,acc)
            in
            let (matched,rl) = aux f ([],(def [] (List.length sl))) fl in
            (matched,List.map2 (fun e l  -> (e,l)) sl rl)

        let rec list_uniq = function 
          | [] -> []
          | h::[] -> [h]
          | h1::h2::tl when h1 = h2 -> list_uniq (h2 :: tl) 
          | h1::tl -> h1 :: list_uniq tl

        let rec filter_map f =
          function
          | [] -> []
          | hd :: tl ->
              (match f hd with
              | None -> filter_map f tl
              | Some v -> v :: filter_map f tl)

    end

end
