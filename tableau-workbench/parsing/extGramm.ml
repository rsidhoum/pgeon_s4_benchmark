(*pp camlp5o -I . pa_extend.cmo q_MLast.cmo *)

open Parselib
open Keywords
open Genlex 
open PcamlGramm

let loc = Stdpp.dummy_loc
let create_gramm = PcamlGramm.create_gramm
let create_obj = PcamlGramm.create_obj

module ExprEntry = EntryMake(struct type t = MLast.expr let ttype = TExpr end) 
module PattEntry = EntryMake(struct type t = MLast.patt let ttype = TPatt end) 
module ExprSchemaEntry = EntryMake(struct type t = Ast.ex_term let ttype = TExprSchema end) 
module PattSchemaEntry = EntryMake(struct type t = Ast.pa_term let ttype = TPattSchema end) 

let formula_expr = ExprEntry.add_entry "formula" ; ExprEntry.get_entry "formula"
let formula_patt = PattEntry.add_entry "formula" ; PattEntry.get_entry "formula"
let formula_expr_schema =
    ExprSchemaEntry.add_entry "formula" ;
    ExprSchemaEntry.get_entry "formula"
let formula_patt_schema =
    PattSchemaEntry.add_entry "formula" ;
    PattSchemaEntry.get_entry "formula"

let expr_expr = ExprEntry.add_entry "expr" ; ExprEntry.get_entry "expr"
let expr_patt = PattEntry.add_entry "expr" ; PattEntry.get_entry "expr"
let expr_expr_schema = create_gramm "expr_expr_schema"
let expr_patt_schema = create_gramm "expr_patt_schema"
let blanumseq : Ast.numcont array Grammar.Entry.e = create_gramm "blanumseq"
let bladenseq : Ast.dencont array Grammar.Entry.e = create_gramm "bladenseq"
let numseq = create_gramm "numseq"
let denseq = create_gramm "denseq"
let node : (Ast.numerator * Ast.ruletype * (Ast.denominator list * Ast.branchcond)) Grammar.Entry.e = create_gramm "node"
let num = create_gramm "num"
let denlist = create_gramm "denlist"

let conn_table = Hashtbl.create 17
let new_conn = function
    |[] -> assert(false)
    |l ->
        try Hashtbl.find conn_table l
        with Not_found ->
            let e = new_co "Conn" in
            let _ = Hashtbl.add conn_table l e
            in e

let forbidden_symbol s name =
    let l = ["|";"||";"|||";"(";")";";"] in
    match name with
    |"formula" |"node" |"expr" -> List.mem s l
    |_ -> false

let make_token ttype self = function
    |Lid("") -> 
            begin match ttype with
            |TExpr | TPatt -> Gramext.Stoken ("LIDENT", "")
            |TExprSchema | TPattSchema -> Gramext.Snterm (create_obj test_uid)
            | _ -> assert(false)
            end
    |Lid(s) when self = s -> Gramext.Sself 
    |Lid(s) -> 
            begin match ttype with
            |TExpr -> Gramext.Snterm (create_obj (ExprEntry.get_entry s))
            |TPatt -> Gramext.Snterm (create_obj (PattEntry.get_entry s))
            |TExprSchema -> Gramext.Snterm (create_obj (ExprSchemaEntry.get_entry s))
            |TPattSchema -> Gramext.Snterm (create_obj (PattSchemaEntry.get_entry s))
            | _ -> assert(false)
            end
    |Type(_) ->
            begin match ttype with
            |TExpr | TExprSchema -> Gramext.Snterm (create_obj Pcaml.expr)
            |TPatt | TPattSchema -> Gramext.Snterm (create_obj Pcaml.patt)
            | _ -> assert(false)
            end
    |List(s) ->
            begin match ttype with
            |TExpr -> Gramext.Slist1sep (
                        Gramext.Snterm (create_obj (ExprEntry.get_entry s)),
                        Gramext.Stoken ("", ";"), false)
            |TPatt -> Gramext.Slist1sep (
                        Gramext.Snterm (create_obj (PattEntry.get_entry s)),
                        Gramext.Stoken ("", ";"), false)
            |TExprSchema -> Gramext.Slist1sep (
                        Gramext.Snterm (create_obj (ExprSchemaEntry.get_entry s)),
                        Gramext.Stoken ("", ";"), false)
            |TPattSchema -> Gramext.Slist1sep (
                        Gramext.Snterm (create_obj (PattSchemaEntry.get_entry s)),
                        Gramext.Stoken ("", ";"), false)
            | _ -> assert(false)
            end
(*    |Symbol(s) when Hashtbl.mem symbol_table s ->
            if forbidden_symbol s self then failwith (Printf.sprintf
            "The symbol \"%s\" is not allowed in the entry %s" s self)
            else Gramext.Stoken ("", s)
*)
    |Symbol(s) -> Gramext.Stoken ("", s)
    |Const(s) ->  Gramext.Stoken ("", s) 
    |Expr -> 
            begin match ttype with
            |TExpr -> Gramext.Snterm (create_obj Pcaml.expr)
            |_-> assert(false)
            end
    |Patt -> 
            begin match ttype with
            |TPatt -> Gramext.Stoken ("", "_")
            |_-> assert(false)
            end
    |Atom -> 
            begin match ttype with
            |TExpr | TPatt -> Gramext.Snterm (create_obj test_uid)
            |TExprSchema | TPattSchema -> Gramext.Stoken ("LIDENT", "")
            | _ -> assert(false)
            end

let make_entry_patt self token_list =
    let gen_action = function
        |[Atom] -> fun l ->      <:patt< `Atom($List.hd l$) >>
        |[Const(s)] -> fun l ->  <:patt< `$s$ >>
        |[Lid(_)] -> fun l ->    <:patt< $List.hd l$ >>
        |[Type(_)] -> fun l ->   <:patt< $List.hd l$ >>
        |[Patt] -> fun l ->      <:patt< _ >>
        |[Expr] -> fun l ->      assert(false)
        |Type(_) :: Symbol(":") :: _ -> fun l -> <:patt< ($list:l$) >>
        |Symbol("(")::_ -> fun l -> <:patt< $List.hd l$ >>
        |tl -> let id = new_conn tl in fun l -> <:patt< `$id$($list:l$) >>
    in
    let actiontbl = Hashtbl.create 17 in
    let args : MLast.patt list ref = ref [] in
    let el = List.map (make_token TPatt self) token_list in
    let _ = 
        if Hashtbl.mem actiontbl token_list then ()
        else Hashtbl.add actiontbl token_list (gen_action token_list)
    in
    let build_action t x =
        if Obj.tag x = Obj.string_tag then
            match t with
            |Symbol(_) -> ()
            |Atom ->          args := <:patt< $lid:String.lowercase (Obj.magic x)$ >> :: !args
            |Const(_) ->      args := <:patt< `$(Obj.magic x)$ >> :: !args
            (* |Lid("int") ->    args := <:patt< $int:(Obj.magic x)$ >> :: !args 
            |Lid("string") -> args := <:patt< $str:(Obj.magic x)$ >> :: !args *)
            |List(_) ->       args := <:patt< $lid:(Obj.magic x)$ >> :: !args 
            |Lid(_) ->        args := <:patt< $lid:(Obj.magic x)$ >> :: !args 
            |Patt ->          args := <:patt< $(Obj.magic x)$ >> :: !args 
            |Type(_) | Expr -> assert(false)
        else args := (Obj.magic x) :: !args
    in
    let action =
      List.fold_left (fun a t -> Obj.magic (fun ex -> build_action t ex ; a))
      (Obj.magic (fun _loc ->
          let l = !args in
          args := [] ;
          try (Hashtbl.find actiontbl token_list) l
          with Not_found -> assert(false))
      ) token_list
    in
    (el,Gramext.action (Obj.repr action))

let make_entry_expr self token_list =
    let token_list = token_list in
    let gen_action = function
        |[Atom] -> fun l ->     <:expr< `Atom($List.hd l$) >>
        |[Const(s)] -> fun l -> <:expr< `$s$ >>
        |[Lid(_)] -> fun l ->   <:expr< $List.hd l$ >>
        |[Type(_)] -> fun l ->  <:expr< $List.hd l$ >>
        |Type(_) :: Symbol(":") :: _ -> fun l -> <:expr< ($list:l$) >>
        |Symbol("(")::_ -> fun l -> <:expr< $List.hd l$ >>
        |Symbol("{")::_ -> fun l -> <:expr< $List.hd l$ >>
        |tl -> let id = new_conn tl in fun l -> <:expr< `$id$($list:l$) >>
    in
    let actiontbl = Hashtbl.create 17 in
    let args : MLast.expr list ref = ref [] in
    let el = List.map (make_token TExpr self) token_list in
    let _ = 
        if Hashtbl.mem actiontbl token_list then ()
        else Hashtbl.add actiontbl token_list (gen_action token_list)
    in
    let build_action t x =
        if Obj.tag x = Obj.string_tag then
            match t with
            |Symbol(_) -> ()
            |Atom ->          args := <:expr< $str:(Obj.magic x)$ >> :: !args
            |Const(_) ->      args := <:expr< $str:(Obj.magic x)$ >> :: !args
            |Lid("int") ->    args := <:expr< $int:(Obj.magic x)$ >> :: !args 
            |Lid("string") -> args := <:expr< $str:(Obj.magic x)$ >> :: !args 
            |List(_) ->       args := <:expr< $lid:(Obj.magic x)$ >> :: !args 
            |Lid(_) ->        args := <:expr< $lid:(Obj.magic x)$ >> :: !args 
            |Expr ->          args := <:expr< $lid:(Obj.magic x)$ >> :: !args 
            |Type(_) | Patt -> assert(false)
        else args := (Obj.magic x) :: !args
    in
    let action =
      List.fold_left (fun a t -> Obj.magic (fun ex -> build_action t ex ; a))
      (Obj.magic (fun _loc ->
          let l = !args in
          args := [] ;
          try (Hashtbl.find actiontbl token_list) l
          with Not_found ->  assert(false))
      ) token_list
    in
    (el,Gramext.action (Obj.repr action))

let make_entry_expr_schema self token_list =
    let gen_action tl =
        match tl with
        |[Atom] |[Const(_)] |[Lid(_)] |Symbol("(")::_ -> fun l -> List.hd l
        |_ -> let id = new_conn tl in fun l -> Ast.ExConn(id,l)
    in
    let actiontbl = Hashtbl.create 17 in
    let args : Ast.ex_term list ref = ref [] in
    let el = List.map (make_token TExprSchema self) token_list in
    let _ = 
        if Hashtbl.mem actiontbl token_list then ()
        else Hashtbl.add actiontbl token_list (gen_action token_list)
    in
    let build_action t x =
        let x' = Obj.magic x in
        if Obj.tag x = Obj.string_tag then
            match t with
            |Symbol(_) -> ()
            |Atom ->            args := Ast.ExAtom(x') :: !args
            |Const(_) ->        args := Ast.ExCons(x') :: !args
            |Lid("") ->         args := Ast.ExVar(x') :: !args 
            |Lid(s) |List(s) -> args := Ast.ExVar(x') :: !args 
            |Type(_) | Expr | Patt -> assert(false) 
        else args := x' :: !args
    in
    let action =
      List.fold_left (fun a t -> Obj.magic (fun ex -> build_action t ex ; a))
      (Obj.magic (fun _loc ->
          let l = !args in
          args := [] ;
          try (Hashtbl.find actiontbl token_list) l
          with Not_found ->  assert(false))
      ) token_list
    in
    (el,Gramext.action (Obj.repr action))

let make_entry_patt_schema self token_list =
    let gen_action = function
        |[Atom] |[Const(_)] |[Lid(_)] |Symbol("(")::_ -> fun l -> List.hd l
        |tl -> let id = new_conn tl in fun l -> Ast.PaConn(self,id,l)
    in
    let actiontbl = Hashtbl.create 17 in
    let args : Ast.pa_term list ref = ref [] in
    let el = List.map (make_token TPattSchema self) token_list in
    let _ = 
        if Hashtbl.mem actiontbl token_list then ()
        else Hashtbl.add actiontbl token_list (gen_action token_list)
    in
    let build_action t x =
        let x' = Obj.magic x in
        if Obj.tag x = Obj.string_tag then
            match t with
            |Symbol(_) -> ()
            |Atom ->            args := Ast.PaAtom(self,x') :: !args
            |Const(_) ->        args := Ast.PaCons(self,x') :: !args
            |Lid("") ->         args := Ast.PaVar(self,x') :: !args 
            |Lid(s) |List(s) -> args := Ast.PaVar(s,x') :: !args 
            |Type(_) |Expr |Patt -> assert(false)
        else args := x' :: !args
    in
    let action =
      List.fold_left (fun a t -> Obj.magic (fun ex -> build_action t ex ; a))
      (Obj.magic (fun _loc ->
          let l = !args in
          args := [] ;
          try (Hashtbl.find actiontbl token_list) l
          with Not_found -> assert(false))
      ) token_list
    in
    (el,Gramext.action (Obj.repr action))

let extend_schema = 
    let aux1 s sep =
        let parse_sep strm =
            match Stream.peek strm with
            |Some (_, token) when token = sep -> Stream.junk strm; token
            |_ -> raise Stream.Failure
        in
        let sep_entry =
            Grammar.Entry.of_parser Pcaml.gram (new_id "separator") parse_sep
        in
        EXTEND
        expr_expr: [
            [ex = Pcaml.expr; sep_entry; sc = formula_expr -> <:expr< ($ex$,$sc$) >>]];
        expr_patt: [
            [pa = Pcaml.patt; sep_entry; sc = formula_patt -> <:patt< ($pa$,$sc$) >>]];

        expr_expr_schema: [[ex = Pcaml.expr; sep_entry; sc = formula_expr_schema ->
                    Ast.ExLabt(loc,(s,ex),sc)]];
        expr_patt_schema: [[pa = Pcaml.patt; sep_entry; sc = formula_patt_schema ->
                    Ast.PaLabt((s,pa),sc)]];
        END
    in
    let aux2 () =
        EXTEND
        expr_expr: [[sc = formula_expr -> sc]];
        expr_patt: [[sc = formula_patt -> sc]];

        expr_expr_schema: [[sc = formula_expr_schema -> Ast.ExTerm(loc,sc)]];
        expr_patt_schema: [[sc = formula_patt_schema -> Ast.PaTerm(sc)]];
        END
    in function
        |[Type(List(s)) :: Symbol(sep) :: _] -> aux1 (s^" list") sep
        |[Type(Lid(s)) :: Symbol(sep) :: _] -> aux1 s sep
        |_ -> aux2 ()

let extend_sequent_node (_,l) =
    let extend_seq cont token_list =
        let gen_action _ = fun l -> Array.of_list l in
        let actiontbl = Hashtbl.create 17 in
        let args = ref [] in
        let el = 
            filter_map (function
                |Type(_) -> Some(Gramext.Snterm (create_obj cont))
                |Symbol(s) -> Some(Gramext.Stoken ("", s))
                |_ -> None
            ) token_list
        in
        let _ = 
            if Hashtbl.mem actiontbl token_list then ()
            else Hashtbl.add actiontbl token_list (gen_action token_list)
        in
        let build_action t x =
            let x' = Obj.magic x in
            match t with
            |Symbol(_) -> ()
            |Type(_) -> args := x' :: !args
            |_ -> assert(false)
        in
        let action =
          List.fold_left (fun a t -> Obj.magic (fun ex -> build_action t ex ; a))
          (Obj.magic (fun _loc ->
              let l = !args in
              args := [] ;
              try (Hashtbl.find actiontbl token_list) l
              with Not_found -> assert(false))
          ) token_list
        in
        (el,Gramext.action (Obj.repr action))
    in
    EXTEND node: [[ dl = denlist; t = test_sep; n = num -> (n,t,dl) ]]; END; 
    Grammar.extend
    [ (create_obj blanumseq, None, [None, None, List.map (extend_seq numseq) l ]);
      (create_obj bladenseq, None, [None, None, List.map (extend_seq denseq) l ]) 
    ]

let extend_tableau_node () =
    EXTEND
      node: [[ n = num; t = test_sep; dl = denlist -> (n,t,dl) ]];
      bladenseq: [[d = denseq -> [|d|] ]];
      blanumseq: [[n = numseq -> [|n|] ]];
    END

let expand_mapcont (_,l) =
    let newl = filter_map (function
        |Type(Lid "set") -> Some(<:expr< (new TwbContSet.map match_schema) >>)
        |Type(Lid "mset") -> Some(<:expr< (new TwbContMSet.map match_schema) >>)
        |Type(Lid "singleton") -> Some(<:expr< (new TwbContSingleton.map match_schema) >>)
        |Symbol(_) -> None
        |_ -> assert(false)
    ) (List.hd l)
    in 
    Hashtbl.add expr_table "mapcont" (<:expr< [| $list:List.rev newl$ |] >>) 

let extend_node_type = function
    |[] -> extend_tableau_node () ; expand_mapcont ("node",[[Type(Lid "set")]])
    |[l] -> extend_sequent_node l ; expand_mapcont l
    |_ -> assert(false)

let rec create_levels label (l1,l2,l3) = function
    |(Symbol(_)::_ as h ) :: tl -> create_levels label (h::l1,l2,l3) tl
    |(Lid(s)::_ as h) :: tl when s = label -> create_levels label (l1,h::l2,l3) tl
    |h :: tl -> create_levels label (l1,l2,h::l3) tl
    |[] -> (l1,l2,l3) 

let extend_entry label entrylist =
    let (symlev,selflev,otherlev) = create_levels label ([],[],[]) entrylist in

    Grammar.extend [ create_obj (ExprEntry.get_entry label), None,
    [None, None, List.map (make_entry_expr label) selflev;
     None, Some Gramext.RightA, List.map (make_entry_expr label) symlev;
     None, None, List.map (make_entry_expr label) otherlev]
    ];

    Grammar.extend [ create_obj (PattEntry.get_entry label), None,
    [None, None, List.map (make_entry_patt label) selflev;
     None, Some Gramext.RightA, List.map (make_entry_patt label) symlev;
     None, None, List.map (make_entry_patt label) otherlev]
    ];

    Grammar.extend [ create_obj (ExprSchemaEntry.get_entry label), None,
    [None, None, List.map (make_entry_expr_schema label) selflev;
     None, Some Gramext.RightA, List.map (make_entry_expr_schema label) symlev;
     None, None, List.map (make_entry_expr_schema label) otherlev]
    ];

    Grammar.extend [ create_obj (PattSchemaEntry.get_entry label), None,
    [None, None, List.map (make_entry_patt_schema label) selflev;
     None, Some Gramext.RightA, List.map (make_entry_patt_schema label) symlev;
     None, None, List.map (make_entry_patt_schema label) otherlev]
    ];

    Grammar.extend
    [
        (create_obj (ExprEntry.get_entry label), 
        None, [None, None, [make_entry_expr label [Symbol("{");Expr;Symbol("}")]] ]);
        (create_obj (PattEntry.get_entry label), 
        None, [None, None, [make_entry_patt label [Patt]] ]);
    ]

let expand_expr_constructor label =
    let ex = (ExprEntry.get_entry label) in
    let px = (PattEntry.get_entry label) in
    let elid = add_lid label in
    let plid = add_lid label in
    EXTEND
        Pcaml.expr: LEVEL "simple" [
            [ elid; "("; e = ex; ")" -> <:expr< ( $e$ : $lid:label$ ) >>
        ]];

        Pcaml.patt: [
            [ plid; "("; "_"; ")" -> <:patt< #$list:[label]$ >>
            | plid; "("; p = px; ")" -> <:patt< $p$ >>
        ]];
    END

(* we write a file with the marshalled representation of the grammar
 * to be then reused in other modules.
 * see the directive : source Modulename *)
let writegramm gramms =
    let tmp_dir =
        let str = "/tmp/twb" ^ Sys.getenv("LOGNAME") in
        let _ =
            try ignore(Unix.stat str) with
            |Unix.Unix_error(_) -> ignore(Unix.mkdir str 0o755)
        in str ^ "/"
    in
    let str =
        let s = (String.lowercase !Pcaml.input_file) in
        let re = Str.regexp "\\([a-zA-z0-9]+\\)\\.ml" in
        Str.replace_first re "\\1" s
    in
    (* write the grammar definition to a file *)
    let ch = open_out (tmp_dir^str^".gramm") in
    Marshal.to_channel ch (!symbol_table,gramms) [];
    close_out ch

(*
let readgramm extmodule gramms = 
    match extmodule with None -> gramms
    |Some(m) ->
        let tmp_dir =
            let str = "/tmp/twb" ^ Unix.getlogin () in
            let _ =
                try ignore(Unix.stat str) with
                |Unix.Unix_error(_) -> ignore(Unix.mkdir str 0o755)
            in str ^ "/"
        in
        let ch = open_in (tmp_dir^String.lowercase m^".gramm") in
        let (_,_,gl) = Marshal.from_channel ch in
        let _ = close_in ch in
        let merge l1 l2 =
            let tab = Hashtbl.create 17 in
            let _ =
                List.iter (function
                    ("expr",r1) -> Hashtbl.replace tab "expr" r1
                    |(id,r1) ->
                        try let r2 = Hashtbl.find tab id in
                            Hashtbl.replace tab id (unique (r1@r2))
                        with Not_found -> Hashtbl.add tab id r1
                ) (l1@l2)
            in Hashtbl.fold (fun k v acc -> (k,v)::acc) tab []
        in List.rev (merge gramms (List.rev gl))
*)

let readgramm m = 
    let tmp_dir =
        let str = "/tmp/twb" ^ Sys.getenv("LOGNAME") in
        let _ =
            try ignore(Unix.stat str) with
            |Unix.Unix_error(_) -> 
                    begin Printf.eprintf "Notice: create directory %s\n" str;
                    ignore(Unix.mkdir str 0o755) end
        in str ^ "/"
    in
    let ch =
        try open_in (tmp_dir^String.lowercase m^".gramm")
        with Sys_error _ -> 
            failwith (Printf.sprintf
            "Dependency error: The current file depends on the file %s.ml. Compile the file %s.ml first" 
            (String.lowercase m) (String.lowercase m))
    in
    let (symbollist,gramms) = Marshal.from_channel ch in
    let _ = close_in ch in
    (symbollist,gramms)

let extgramm gramms =
    List.iter (function
        |("expr",rules) ->
                extend_schema rules;
        |(id,rules) ->
                PattEntry.add_entry id;
                ExprEntry.add_entry id;
                ExprSchemaEntry.add_entry id; 
                PattSchemaEntry.add_entry id; 
                extend_entry id rules;
    ) gramms;
    (* DEBUG stuff *)
    List.iter (fun (id,rules) ->
        Options.print (Printf.sprintf "%s_patt_schema:\n" id);
        List.iter (fun tl ->
            Options.print (PcamlGramm.stype_list_to_string tl)
        ) rules;
        Options.print (Printf.sprintf "\n");
    ) gramms;
    Options.print (PattSchemaEntry.entries_to_string ());
    Options.print (ExprEntry.entries_to_string ())

let expand_constructors = 
    List.iter (fun (id,_) -> expand_expr_constructor id )

let make_type_decl (loc, name) tyv cty ctyl =
  let typevars =
      List.map (fun (id, _) -> (vala (Some id), None)) tyv
  in
  { MLast.tdNam = vala (loc, vala name);
    MLast.tdPrm = vala typevars;
    MLast.tdPrv = vala true;
    MLast.tdDef = cty;
    MLast.tdCon = vala ctyl }

let expand_grammar_type (id,rules) =
    let typevars = ref [(id,(false,false))] in
    let open_type = function
        |Lid(s)  when s = id -> <:ctyp< '$s$ >>
        |List(s) when s = id -> <:ctyp< list '$s$ >>
        |Lid(s)  -> typevars := (s,(false,false))::!typevars ; <:ctyp< '$s$ >>
        |List(s) -> typevars := (s,(false,false))::!typevars ; <:ctyp< list '$s$ >>
        |Atom -> <:ctyp< [= `Atom of string ] >>
        |Const(s) -> <:ctyp< [= `$s$ ] >>
        |_ -> assert(false)
    in
    let closed_type = function
        |Lid(s) -> <:ctyp< $lid:s$ >>
        |List(s) -> <:ctyp< list $lid:s$ >>
        |Atom -> <:ctyp< [= `Atom of string ] >>
        |Const(s) -> <:ctyp< [= `$s$ ] >>
        |_ -> assert(false)
    in
    let build_fields inherited_type exptype =
      let aux = function
        |[Lid("")] -> None
        |[Lid(s)] -> Some("",[inherited_type s])
        |[Type(t);Symbol(":");Lid(s)] ->
                Some("",[<:ctyp< ($exptype t$ * $exptype (Lid s)$) >>])
        |[Atom] -> Some("Atom",[<:ctyp< string >>])
        |[Const(s)] -> Some(s,[])
        |Symbol("(") :: _ -> None
        |l ->
                let args = filter_map (function
                    |Symbol(_) |Type(_) -> None
                    |t -> Some(exptype t)
                    ) l
                in Some(new_conn l,List.rev args)
      in
        match List.rev (filter_map aux rules) with
        |[] -> assert(false)
        |l ->
            let aux = function
                |("", [t]) -> MLast.PvInh (loc, t)
                |(id, []) -> MLast.PvInh (loc, <:ctyp< [= `$id$ ] >>)
                |(id, args) -> MLast.PvInh (loc, <:ctyp< [= `$id$ of ($list:args$) ] >>)
            in
            let l = List.map aux l
            in <:ctyp< [= $list:l$ ] >>
    in
    let open_inherited_type s =
        typevars := (s,(false,false))::!typevars;
        <:ctyp< $lid:s^"_open"$ '$s$ >>
    in
    let fields = build_fields open_inherited_type open_type in
    let closed_fields =
        build_fields (fun s -> <:ctyp< $lid:s$ >>) closed_type
    in
    let t1 = make_type_decl (loc,id^"_open") (unique !typevars) fields [] in
    let t2 = make_type_decl (loc,id) [] closed_fields [] in
    [t1;t2]

let rec expand_grammar_expr_type = function
    |[[Lid(s)]] ->   <:ctyp< $lid:s$ >>
    |[[Atom]] ->     <:ctyp< string >>
    |[[Const(s)]] -> <:ctyp< [= `$s$ ] >>
    |[[List(s)]] ->  <:ctyp< list $lid:s$ >>
    |[[Type(t);Symbol(":");r]]  -> 
            <:ctyp< ($expand_grammar_expr_type [[t]]$ *
            $expand_grammar_expr_type [[r]]$) >>
    |_ -> assert(false)
    
let expand_grammar_type_list gramms =
    List.map (function
        |("expr",rules) -> 
                [make_type_decl (loc,"expr") [] (expand_grammar_expr_type rules) []]
        |(id,rules) -> expand_grammar_type (id,rules)
    ) gramms

let expand_grammar_syntax_list gramms =
    let rec aux1 = function
        | Atom -> <:expr< InputParser.PcamlGramm.Atom >>
        | Const s -> <:expr< InputParser.PcamlGramm.Const $str:s$ >>
        | Symbol s -> <:expr< InputParser.PcamlGramm.Symbol $str:s$ >>
        | Lid s -> <:expr< InputParser.PcamlGramm.Lid $str:s$ >>
        | List s -> <:expr< InputParser.PcamlGramm.List $str:s$ >>
        | Type s -> <:expr< InputParser.PcamlGramm.Type $aux1 s$ >>
        | Patt -> <:expr< InputParser.PcamlGramm.Patt >>
        | Expr -> <:expr< InputParser.PcamlGramm.Expr >>
    in
    let aux2 rules = list_to_exprlist (
        List.map (fun l ->
            list_to_exprlist (List.map aux1 l) 
            ) rules
        )
    in
    let e = list_to_exprlist (
        List.map (function |(id,rules) ->
            <:expr< ($str:id$,$aux2 rules$) >>
            ) gramms
        )
    in <:str_item< value __gramms = $e$ >>

let expand_printer gramm =
    let aux (name,rules) = 
        let gen_pel = function
            |[Atom] ->
                    Some(<:patt< `Atom( a ) >>,vala None,
                    <:expr< Printf.sprintf "%s" a >>)
            |[Const(s)] -> 
                    Some(<:patt< `$s$ >>,vala None,
                    <:expr< Printf.sprintf $str:s$  >>)
            |[Lid("")] |[Type(_)] |[Patt] |[Expr] 
            |Symbol("("):: _ -> None
            |[Lid(id)] ->
                    Some(<:patt< ( #$list:[id]$ as f ) >>,vala None,
                     <:expr< $lid:id^"_printer"$ f >>)
            |Type(_) :: Symbol(":") :: Lid(id) :: _ ->
                    Some(<:patt< (_,f) >>,vala None,
                     <:expr< $lid:id^"_printer"$ f >>)
            |tl ->
                    let f =
                        List.fold_left (fun s i ->
                            if s = "" then i else Printf.sprintf "%s %s" s i
                        ) "" (List.map (function |Symbol(s) -> s |_ -> "%s") tl) 
                    in
                    let (l,_) =
                        List.fold_left (fun (acc,i) s -> 
                            match s with
                            |Symbol(_) -> (acc,i)
                            |Lid(id) -> (("c"^string_of_int i,id)::acc,i+1)
                            |Atom -> (("c"^string_of_int i,"")::acc,i+1)
                            |_ -> assert(false)
                        ) ([],0) tl
                    in
                    let exl =
                        List.map (function
                            |(e,"") -> <:expr< Printf.sprintf "%s" $lid:e$ >>
                            |(e,id) -> <:expr< $lid:id^"_printer"$ $lid:e$ >>
                        ) (List.rev l)
                    in 
                    let pal = List.map (function
                        |(e,"") -> <:patt< `Atom $lid:e$ >>
                        |(e,_) -> <:patt< $lid:e$ >>
                        ) (List.rev l)
                    in 
                    let id = new_conn tl in
                    Some(
                        <:patt< `$id$($list:pal$) >>,vala None,
                        List.fold_left (fun a e ->
                            <:expr< $a$ $e$ >>
                        ) <:expr< Printf.sprintf $str:"("^f^")"$  >> exl
                        )
        in
        (<:patt< $lid:name^"_printer"$ >>,
        <:expr< fun [ $list:filter_map gen_pel rules$ ] >>)
    in <:str_item< value rec $list:List.map aux gramm$ >>

let expand_ast2input gramm =
    let aux (name,rules) = 
        let gen_pel = function
            |[Atom] -> Some(<:patt< Ast.ExAtom a >>,vala None, <:expr< `Atom a >>)
            |[Const(_)] |[Lid(_)] |[Type(_)] |[Patt] |[Expr] 
            |Type(_) :: Symbol(":") :: _
            |Symbol("("):: _ -> None
            |tl ->
                    let (l,_) =
                        List.fold_left (fun (acc,i) s -> 
                            match s with
                            |Symbol(_) -> (acc,i)
                            |Lid(id) -> (("c"^string_of_int i,id)::acc,i+1)
                            |Atom -> (("c"^string_of_int i,"")::acc,i+1)
                            |_ -> assert(false)
                        ) ([],0) tl
                    in
                    let exl =
                        List.map (function
                            |(e,"") -> <:expr< `Atom $lid:e$ >>
                            |(e,id) -> <:expr< $lid:id^"_ast2input"$ $lid:e$ >>
                        ) (List.rev l)
                    in 
                    let pal = List.map (function
                        |(e,"") -> <:patt< Ast.ExAtom $lid:e$ >>
                        |(e,_) -> <:patt< $lid:e$ >>
                        ) (List.rev l)
                    in 
                    let id = new_conn tl in
                    Some(
                        <:patt< Ast.ExConn($str:id$,$list_to_pattlist pal$) >>,vala None,
                        <:expr< `$id$($list:exl$) >>
                        )
        in
        let const = Hashtbl.fold( fun k (l,o) acc ->
            if l = name && o = "formula" then
                (<:patt< Ast.ExCons($str:k$) >>,
                vala None,<:expr< `$k$>>)::acc
            else acc
            ) const_table []
        in
        let def = <:patt< _ >>, vala None, <:expr< assert(False) >> in
        (<:patt< $lid:name^"_ast2input"$ >>,
        <:expr< fun [ $list:(filter_map gen_pel rules)@const@[def]$ ] >>)
    in <:str_item< value rec $list:List.map aux gramm$ >>

let remove_node_entry = List.filter (fun (l,_) -> not(l = "node"))
let select_node_entry = List.filter (fun (l,_) -> l = "node")
let update_gramm_table gramms =
    let tb = (Hashtbl.create 17) in
    let _ = List.iter (fun (k,v) -> Hashtbl.add tb k v) gramms in 
    let rec aux orig label rules =
        List.iter(function
            |[Const(u)] -> 
                    if Hashtbl.mem const_table u && orig = "formula" then
                        if orig = "formula" then
                            Hashtbl.replace const_table u (label,orig)
                        else ()
                    else Hashtbl.add const_table u (label,orig)
            |[Lid(id)] when not(id = label) && not(id = "") && (orig = "formula") ->
                    aux orig label (Hashtbl.find tb id)
            |_ -> ()
        ) rules
    in
    List.iter (function
        |("node",_) -> () 
        |("expr",[Type(t)::[Symbol(":");Lid(_)]]) ->
                begin match t with
                |List(s) -> Hashtbl.add gramm_table (s ^ " list") ()
                |Lid(s)  -> Hashtbl.add gramm_table s ()
                |_ -> assert(false)
                end
        |("expr",_) -> ()
        |(n,rules) -> Hashtbl.add gramm_table n (); aux n n rules
    ) gramms

EXTEND
GLOBAL: Pcaml.str_item; 

Pcaml.str_item: [[
    "CONNECTIVES"; "["; l = LIST1 connective SEP ";"; "]" -> <:str_item< "" >>

    |"GRAMMAR"; gramms = LIST1 gramm; "END" ->
            let withoutnode = remove_node_entry gramms in
            let _   = writegramm gramms in
            let _   = update_gramm_table gramms in
            let _   = extgramm withoutnode in
            let _   = expand_constructors withoutnode in
            let _   = extend_node_type (select_node_entry gramms) in 
            let sl  = expand_grammar_syntax_list gramms in
            let ty  = List.flatten (expand_grammar_type_list withoutnode) in
            let sty = <:str_item< type $list:ty$ >> in
            let pr  = expand_printer withoutnode in
            let ast = expand_ast2input withoutnode in
            <:str_item< declare
            module GrammTypes = struct $list:[sty;pr;ast;sl]$ end;
            open GrammTypes;
            end >>
]];

gramm: [
    [ exprid ; ":=" ; t = ptype ; e = OPT [ ":" ; p = plid -> p ]; ";;" ->
          begin match e with
          |None -> ("expr", [[t]])
          |Some(l) -> ("expr",[Type(t)::[Symbol(":");Lid(l)]])
          end
  
    | nodeid ; ":="; c = cont ; l = LIST0 [ s = symbol; c = cont -> s@[c] ] ; ";;" ->
            ("node",[c::(List.flatten l)])
        
    | p = test_lid; ":="; rules = LIST1 rule SEP "|" ; ";;" ->
            let var = [[Lid("")]] in
            let par = [[Symbol("(");Lid(p);Symbol(")")]] in
            (p,rules@var@par) 
]];

cont: [
    [ setid -> Type(Lid "set")
    | msetid -> Type(Lid "mset")
    | singletonid -> Type(Lid "singleton") 
]];

rule: [[ psl = LIST1 psymbol; OPT assoc -> List.flatten psl ]];

assoc: [
    [ "LEFT"  -> Gramext.LeftA
    | "RIGHT" -> Gramext.RightA
    | "NONE"  -> Gramext.NonA ]
];

psymbol: [
    [ "ATOM"  -> [Atom]
    (* | "extend"; m = UIDENT -> Extend(m) *)
    | e = symbol -> e
    | e = ptype -> [e]
    | e = const -> [e]
]];

const: [[ u = UIDENT -> Const(u) ]];

ptype: [
    [ t = plid ; listid -> List(t) 
(*    | l = LIST1 plid SEP "*" -> Tuple(l) *)
    | t = plid -> Lid(t)
]];

plid: [
    [ 
        (* u = UIDENT ; "."; i = LIDENT -> u^"."^i *)
    i = LIDENT -> i 
]];

(*
(* A{s/t} is the formula A with all occurrences of t substituted by s *) 
(* FIXME: the substitution should be possible inside a term... this require
 * to change the ast and re-write the expand_expression_expr function *)
ocaml_expr_term: [
  [x = LIDENT; "{"; s = ocaml_expr_term; "/"; t = ocaml_expr_term; "}" ->
          Ast.Apply("__substitute",[Ast.Term(Ast.Var x);s;t])
  |t = formula_expr -> Ast.Term(t)
]];

*)
END
