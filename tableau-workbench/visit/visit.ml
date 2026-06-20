
module Make(N:Node.S)(R: Rule.S with type node = N.node)
= struct

    open Tree

    type node = R.node
    type rule = R.rule
    type context = R.context

    type res = ((rule * context) * continuation) Llist.llist
    and continuation = Cont of (node -> res) | End
    and m = ((rule * context) * continuation) Llist.llist

    type tactic =
        |Skip
        |Fail
        |Rule of R.rule
        |Seq of tactic * tactic
        |Alt of tactic * tactic * (node result -> bool)
        |FairAlt of tactic * tactic * (node result -> bool)
        |AltCut of tactic * tactic
        |Mu of (string * tactic)
        |Var of string

    module Cache = Cache.Make(N)   
    let table = ref (new Cache.cache true)
    let _ = Random.self_init ()
    
    exception TacticExn

    let rec visit_aux env acc = function
        |Skip -> fun n ->
                begin match acc with
                |[] -> Node(n) (* no more rules applicable *)
                |h::t -> visit_aux env t h n 
                end
        |Fail -> fun _ -> RuleFail
        |Rule(rule) -> fun n ->
                let context = rule#check n in
                let up = rule#up context in
                if context#is_valid then
                    begin match rule#down context,acc with
                    |Leaf(n),_  -> up (Llist.return (Node(n)))
                    |Tree(l),[] -> up (Llist.map (fun n -> Node(n)) l)
                    |Tree(l),h::t ->
                            let visit = memo_visit env ~cache:rule#use_cache t h in
                            let f n =
                                begin match visit n with
                                |RuleFail -> Node(n)
                                |SeqFail -> raise TacticExn
                                |r -> r
                                end
                            in try up (Llist.map f l) with
                            TacticExn -> SeqFail
                    end
                else RuleFail
        |Seq(t1,t2) -> fun n ->
                begin match visit_aux env (t2::acc) t1 n with
                |SeqFail | RuleFail -> SeqFail
                |r -> r
                end
        |AltCut(t1,t2) -> fun n ->
                begin match (visit_aux env acc t1 n) with
                |SeqFail | RuleFail -> (visit_aux env acc t2 n)
                |r -> r
                end
        |FairAlt(t1,t2,cond) -> 
                if (Random.int 2) = 0
                then visit_aux env acc (Alt(t1,t2,cond)) 
                else visit_aux env acc (Alt(t2,t1,cond))
        |Alt(t1,t2,cond) -> fun n ->
                begin match (visit_aux env acc t1 n) with
                |SeqFail | RuleFail -> (visit_aux env acc t2 n)
                |r when cond r -> r
                |_ -> (visit_aux env acc t2 n)
                end
        |Mu(x,t) -> visit_aux ((x,t)::env) acc t
        |Var(x)  ->
                try visit_aux env acc (List.assoc x env)
                with Not_found -> failwith "Variable not defined"

    and memo_visit env ?(cache=false) acc str node =
        if cache then
            try !table#find node
            with Not_found ->
                let res = visit_aux env acc str node in
                !table#add node res;
                res
        else
            visit_aux env acc str node

    let visit cache t n =
        table := cache ; 
        Llist.return (visit_aux [] [] t n)

end
