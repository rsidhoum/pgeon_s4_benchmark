
exception SyntaxError of string

let rec extract_pa_term_vars acc = function
    |Ast.PaConn(_,id,l) -> (List.flatten (List.map (extract_pa_term_vars []) l))
    |Ast.PaCons(_,s) |Ast.PaAtom(_,s) |Ast.PaVar(_,s) -> s::acc
    |Ast.PaHist(s) |Ast.PaVari(s,_) -> s::acc

let rec extract_pa_expr_vars acc = function
    |Ast.PaTerm(t) -> (extract_pa_term_vars [] t)
    |Ast.PaLabt((decolabel,deco),t) -> (extract_pa_term_vars [] t)
    |Ast.PaTupl(l) -> List.flatten (List.map (extract_pa_expr_vars acc) l)
    |Ast.PaPatt(pa) -> acc

let check_numerator arr =
    List.flatten (
        List.flatten (
            Array.to_list (
                Array.mapi (fun index numcontlist ->
                    List.map (fun (arity, pa_expr) ->
                        match arity with
                        |Ast.Single | Ast.Empty -> extract_pa_expr_vars [] pa_expr
                        |Ast.Set -> extract_pa_expr_vars [] pa_expr
                    ) numcontlist
                ) arr
            )
        )
    )

let rec check_ex_term _loc vl = function
    |Ast.ExConn(_,l) -> List.iter (check_ex_term _loc vl) l
    |Ast.ExCons(s) |Ast.ExAtom(s) |Ast.ExVar(s) ->
            if List.mem s vl || Hashtbl.mem Keywords.const_table s ||
               Hashtbl.mem Keywords.hist_table s then ()
            else Stdpp.raise_with_loc _loc (SyntaxError (s^" : Unbounded Variable"))
    |Ast.ExHist(s) |Ast.ExVari(s,_) -> ()

let rec check_ex_expr vl = function
    |Ast.ExAppl(_loc,f,ex_expr) -> check_ex_expr vl ex_expr
    |Ast.ExLabt(_loc,(_,deco),ex_term) -> check_ex_term _loc vl ex_term
    |Ast.ExTerm(_loc,ex_term) -> check_ex_term _loc vl ex_term
    |Ast.ExTupl(_loc,l) -> List.iter (check_ex_expr vl) l
    |Ast.ExExpr(_loc,ex) -> ()

let check_denominator vl = function
    |Ast.Denominator arr -> 
            Array.iteri (fun index dencontlist ->
                List.iter (fun ex_expr ->
                    check_ex_expr vl ex_expr
                ) dencontlist
            ) arr
    |Ast.Status s -> () 

let check_condition vl condlist =
        List.iter (fun (Ast.Condition ex_expr) ->
            check_ex_expr vl ex_expr
        ) condlist

let check_action vl actionlist =
    List.iter (function
        |Ast.Assign(_,ex_expr) -> check_ex_expr vl ex_expr
        |Ast.Function(ex_expr) -> check_ex_expr vl ex_expr
    ) actionlist

let check_rule (Ast.Rule rule) =
    let (name,
        ruletype,
        (Ast.Numerator arr),
        (denlist,bcond),
        condlist,
        actionlist,
        branchcondlist,
        backtracklist,
        cache,
        heurisitic
    ) = rule
    in
    let vl = check_numerator arr in
    List.iter (check_denominator vl) denlist;
    check_condition vl condlist;
    List.iter (check_action vl) actionlist;
    List.iter (check_condition vl) branchcondlist ;
    check_action vl backtracklist

let check_tableau l = List.iter check_rule l
