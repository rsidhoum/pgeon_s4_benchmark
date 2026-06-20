(*pp camlp5o -I . pa_extend.cmo q_MLast.cmo *)

open Genlex
open Parselib
open Keywords
open Tablib

EXTEND
GLOBAL : Pcaml.str_item Pcaml.patt Pcaml.expr ExtGramm.num ExtGramm.denlist
ExtGramm.denseq ExtGramm.numseq ExtGramm.bladenseq ExtGramm.blanumseq;

  Pcaml.expr: LEVEL "simple" [
          [ "tactic"; "("; t = tactic; ")" -> expand_tactic t
  ]];

  Pcaml.str_item: [
      ["HISTORIES"; l = LIST1 history SEP ";"; "END" ->
          expand_histories (Ast.History l)
      |"VARIABLES"; l = LIST1 variable SEP ";"; "END" ->
          expand_histories (Ast.Variable l)
      |"TABLEAU"; l = LIST1 rule; "END" ->
              SyntaxChecker.check_tableau l;
              expand_tableau (Ast.Tableau l)
      |"SEQUENT"; l = LIST1 rule; "END" ->
              SyntaxChecker.check_tableau l;
              expand_tableau (Ast.Tableau l)
      |"STRATEGY"; OPT ":="; t = Pcaml.expr -> expand_strategy t
      |"MAIN" -> expand_main ()
      
      |"SIMPLIFICATION"; OPT ":="; e = Pcaml.expr -> expand_simplification e
      |"PP"; OPT ":="; e = Pcaml.expr -> expand_preproc e
      |"NEG"; OPT ":="; e = Pcaml.expr -> expand_negation e
      |"EXIT"; OPT ":="; f = userfunction -> expand_exit f 
      |"OPTIONS"; l = LIST1 options SEP ";"; "END" -> expand_options l
      |sourceid; m = UIDENT -> expand_source m
  ]];

  history:  [[ name = UIDENT; (t,e) = def -> (name,t,e)]];
  variable: [[ name = LIDENT; (t,e) = def -> (name,t,e)]];
  def: [[ ":"; t = Pcaml.ctyp; ":="; e = Pcaml.expr LEVEL "simple" -> (t,e) ]];

  options : [[
      OPT "(";
        s = STRING ; ",";
        e = Pcaml.expr LEVEL "simple"; ",";
        a = STRING; OPT ")" -> Ast.Options (s,e,a)
  ]];

  tactic:
  [ "One" LEFTA
      [ id = LIDENT -> Ast.TaVar(id)
      | t1 = tactic; ";"; t2 = tactic -> Ast.TaSeq(t1,t2)
      | t1 = tactic; "!"; t2 = tactic -> Ast.TaAltCut(t1,t2)
      | t1 = tactic; "||"; t2 = tactic ->
              Ast.TaAlt(t1,t2,<:expr< tcond "Open" >>)
      | t1 = tactic; "|" ; t2 = tactic ->
              Ast.TaAlt(t1,t2,<:expr< tcond "Close" >>)
      | t1 = tactic; "?||"; t2 = tactic ->
              Ast.TaFairAlt(t1,t2,<:expr< tcond "Open" >>)
      | t1 = tactic; "?|" ; t2 = tactic ->
              Ast.TaFairAlt(t1,t2,<:expr< tcond "Close" >>)
      ]
  |
      [ "("; t = tactic; ")" -> t
(*      | "!"; t = tactic -> Ast.TaCut(t) *)
      | "Skip" -> Ast.TaSkip
      | "Fail" -> Ast.TaFail
      | muid; OPT "("; var = muvar; OPT ")"; "."; t = tactic -> Ast.TaMu(var,t)
      | "("; t = tactic; ")"; "*" ->
              let id = new_id "muvar" in
(*              Ast.TaMu(id,Ast.TaAltCut(Ast.TaSeq(t,Ast.TaMVar(id)),Ast.TaSkip))
 *              *)
                Ast.TaMu(id,Ast.TaAltCut(Ast.TaSeq(t,Ast.TaMVar(id)),Ast.TaSkip))
      | m = UIDENT; "."; r = UIDENT -> Ast.TaModule(m,r)
      | id = test_muvar -> id
      ]
  ];

  rule: [[
      "RULE";
      id = UIDENT;
      (n,t,dl) = ExtGramm.node;
      cl = OPT condition;
      hl = OPT actionlist;
      bl = OPT branchlist; 
      bt = OPT backtracklist;
      he = OPT [ "HEURISTIC"; ":="; f = Pcaml.expr -> f ];
      ca = OPT [ "CACHE";     ":="; c = Pcaml.expr -> c ]; 
      "END" ->
          Ast.Rule (id,t,n,dl,
                    Option.optlist cl,
                    Option.optlist hl,
                    Option.optlist bl,
                    Option.optlist bt,
                    ca, he)
  ]];

  condition: [[
      "COND"; OPT "["; l = LIST1 userfunction SEP ";"; OPT "]" ->
          List.map (fun c -> Ast.Condition c ) l
  ]];

  actionlist: [[
      "ACTION"; OPT "["; l = LIST1 action SEP ";"; OPT "]" -> l
  ]];

  branchlist: [[
      "BRANCH"; OPT "["; l = LIST1 branch SEP ";"; OPT "]" -> l
  ]];

  backtracklist: [[
      "BACKTRACK"; OPT "["; l = LIST1 userback SEP ";"; OPT "]" -> l
  ]];

  branch: [[
      OPT "["; l = LIST0 userfunction SEP ";"; OPT "]" ->
          List.map (fun c -> Ast.Condition c ) l
  ]];

  action: [[
      OPT "["; l = LIST0 useract SEP ";"; OPT "]" -> l
  ]];
  
  userback: [
      [s = test_variable; ":="; f = assignfun ->
          Ast.Assign (Ast.ExVari(s, Ast.Null), f)
      |f = userfunction -> Ast.Function(f)
  ]];
  
  useract: [
      [s = test_history; ":="; f = assignfun -> Ast.Assign (Ast.ExHist s, f)
      |f = userfunction -> Ast.Function(f)
  ]];

  assignfun: [
      [f = funargs -> f
      |f = userfunction -> f
  ]];

  funargs: [
      [x = test_variable; e = varindex -> Ast.ExTerm(loc,Ast.ExVari(x, e))
      |s = test_history  -> Ast.ExTerm(loc,Ast.ExHist s)
   ]];

  userfunction: [
      [f  = LIDENT; "("; args = LIST0 assignfun SEP ","; ")" ->
              Ast.ExAppl(loc,f, Ast.ExTupl(loc,args))
      |t  = ExtGramm.formula_expr_schema -> Ast.ExTerm(loc,t)
      |ex = ExtGramm.expr_expr_schema -> ex
      |ex = Pcaml.expr -> Ast.ExExpr(loc,ex)
    ]];

  varindex: [[
       "@"; allid -> Ast.All
      |"@"; lastid -> Ast.Last
      |"@"; i = INT -> Ast.Int(int_of_string i)
  ]];

  ExtGramm.denlist: [[
       d = den; "|||"; dl = den_user   -> ((d::dl),Ast.User)
      |d = den; "||";  dl = den_exists -> ((d::dl),Ast.Exists)
      |d = den; "|";   dl = den_forall -> ((d::dl),Ast.ForAll)
      |d = den -> ([d],Ast.Linear)
  ]];

  den_user:   [[ dl = LIST1 den SEP "|||" -> dl ]];
  den_exists: [[ dl = LIST1 den SEP "||" -> dl ]];
  den_forall: [[ dl = LIST1 den SEP "|" -> dl ]];

  den: [
      [d = ExtGramm.bladenseq -> Ast.Denominator d
      |s = "Close" -> Ast.Status(s)
      |s = "Open"  -> Ast.Status(s)
      |s = "Stop"  -> Ast.Status(s)
      ]
  ];
  ExtGramm.num: [[ d = ExtGramm.blanumseq -> Ast.Numerator d ]];

  ExtGramm.denseq: [[ d = LIST0 denformula SEP ";" -> d ]];
  ExtGramm.numseq: [[ d = LIST0 numformula SEP ";" -> d ]];
  
  numformula: [
      [ "{"; t = ExtGramm.expr_patt_schema; "}" -> (Ast.Single,t)
      | "("; t = ExtGramm.expr_patt_schema; ")" -> (Ast.Empty,t)
      | t = ExtGramm.expr_patt_schema -> (Ast.Set,t)
      ]
  ];
  
  denformula: [
      [v = test_variable; "@"; i = INT ->
          Ast.ExTerm (loc, Ast.ExVari (v, Ast.Int (int_of_string i)))
      |v = test_history -> Ast.ExTerm(loc, Ast.ExHist(v))
      |f = LIDENT; "("; l = LIST0 args SEP ","; ")" ->
              Ast.ExAppl(loc, f,Ast.ExTupl(loc,l))
      |t = ExtGramm.expr_expr_schema; sl = LIST0 simplification ->
              if sl = [] then t
              else Ast.ExAppl(loc, "__simpl",Ast.ExTupl(loc,t::sl))
      ]
  ];

  args: [
      [f = denformula -> f
      |"["; l = LIST0 denformula SEP ";"; "]" -> Ast.ExTupl(loc,l)
      |e = Pcaml.expr -> Ast.ExExpr(loc, e)
      ]
  ];

  simplification: [[
       "["; t = denformula; "]" -> Ast.ExAppl(loc,"__simplarg",t)
  ]];

END
