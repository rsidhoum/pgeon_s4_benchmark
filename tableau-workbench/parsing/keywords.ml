
module PcamlGramm = Entrylib.Make(struct let gram = Pcaml.gram end)
open PcamlGramm

module LidEntry = EntryMake(struct type t = string let ttype = TLid end)

open Genlex

let (=~) s re = Str.string_match (Str.regexp re) s 0
let get_match i s = Str.matched_group i s

let hist_table  : (string, string * MLast.ctyp * MLast.expr) Hashtbl.t = Hashtbl.create 50
let vars_table  : (string, string * MLast.ctyp * MLast.expr) Hashtbl.t = Hashtbl.create 50
let const_table : (string, (string * string)) Hashtbl.t = Hashtbl.create 50
let tactic_table : (string, unit) Hashtbl.t = Hashtbl.create 50
let expr_table : (string, MLast.expr) Hashtbl.t = Hashtbl.create 50
let gramm_table : (string, unit) Hashtbl.t = Hashtbl.create 17

let symbol_table : (int * (string * string) list ) list ref = ref []
let add_symbol l =
    let sort ll = List.sort (fun (n1,_) (n2,_) -> compare n2 n1) ll in
    symbol_table := sort ( (List.length l,l) :: !symbol_table )

let add_lid lid =
    let strlid lid strm =
        match Stream.peek strm with
        |Some(_,str) when str = lid -> Stream.junk strm; str
        |_ -> raise Stream.Failure
in
LidEntry.add_entry_of_parser (strlid lid) lid ;
LidEntry.get_entry lid

let exprid = add_lid "expr"
let nodeid = add_lid "node"
let formulaid = add_lid "formula"

let setid = add_lid "set"
let msetid = add_lid "mset"
let singletonid = add_lid "singleton"

let listid = add_lid "list"

let sourceid= add_lid "source"

let muid = add_lid "mu"
let allid = add_lid "all"
let lastid = add_lid "last"

let test_lid strm =
    match Stream.peek strm with
    |Some(_,"formula") -> Stream.junk strm; "formula"
    |Some("LIDENT",s) when not(s = "expr") -> Stream.junk strm; s
    |_ -> raise Stream.Failure
let test_lid = Grammar.Entry.of_parser Pcaml.gram "lid" test_lid

let test_uid strm =
    match Stream.peek strm with
    |Some (("UIDENT", s)) when not(Hashtbl.mem const_table s) -> Stream.junk strm; s
    |_ -> raise Stream.Failure
let test_uid = Grammar.Entry.of_parser Pcaml.gram "test_uid" test_uid 

let test_history strm =
    match Stream.peek strm with
    |Some (("UIDENT", s)) when Hashtbl.mem hist_table s -> Stream.junk strm; s
    |_ -> raise Stream.Failure
let test_history = Grammar.Entry.of_parser Pcaml.gram "test_history" test_history 

let test_variable strm =
    match Stream.peek strm with
    |Some (("LIDENT", s)) when Hashtbl.mem vars_table s -> Stream.junk strm; s
    |_ -> raise Stream.Failure
let test_variable = Grammar.Entry.of_parser Pcaml.gram "test_variable" test_variable 

let test_muvar strm =
    match Stream.peek strm with
    |Some("UIDENT",s) when Hashtbl.mem tactic_table s -> Stream.junk strm; Ast.TaMVar(s)
    |Some("UIDENT",s) -> Stream.junk strm; Ast.TaBasic(s)
    |_ -> raise Stream.Failure
let test_muvar = Grammar.Entry.of_parser Pcaml.gram "test_muvar" test_muvar 

let muvar strm =
    match Stream.peek strm with
    |Some("UIDENT",s) -> Stream.junk strm; Hashtbl.replace tactic_table s (); s
    |_ -> raise Stream.Failure
let muvar = Grammar.Entry.of_parser Pcaml.gram "muvar" muvar 

let test_sep strm =
    match Stream.peek strm with
    |Some(_,s) when s =~ "~~+" -> Stream.junk strm; Ast.UnChoice
    |Some(_,s) when s =~ "==+" -> Stream.junk strm; Ast.NoChoice
    |Some(_,s) when s =~ "--+" -> Stream.junk strm; Ast.ExChoice
    |_ -> raise Stream.Failure
let test_sep = Grammar.Entry.of_parser Pcaml.gram "test_sep" test_sep 

let connective strm =
    let get_stream s =
        let lexer = Grammar.glexer Pcaml.gram in
        let (t,_) = lexer.Token.tok_func (Stream.of_string s) in
        let l = Stream.npeek (String.length s) t in
        let (r,_) = List.partition (fun (k,_) -> not(k = "EOI")) l in r
    in
    let s =
        match Stream.peek strm with
        |Some("STRING",s) -> s
        |_ -> raise Stream.Failure
    in
    try
        Stream.junk strm;
        add_symbol (get_stream s)
    with Stream.Failure -> raise Stream.Failure
let connective = Grammar.Entry.of_parser Pcaml.gram "connective" connective

let symbol strm =
    let test strm ll =
        try
            let (_,m) = List.find (fun (n,l) ->
                (Stream.npeek n strm) = l) ll
            in List.map (fun (_,s) -> Symbol(s)) m
        with Not_found -> raise Stream.Failure
    in try
        let l = test strm !symbol_table in
        for i = 0 to (List.length l) - 1 do Stream.junk strm done;
        l
    with Stream.Failure -> raise Stream.Failure
let symbol = Grammar.Entry.of_parser Pcaml.gram "symbol" symbol
