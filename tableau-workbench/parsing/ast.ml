
type options = Options of (string * MLast.expr * string )
type connectives = connective list
and connective = Connective of (string * string * string)
type history =
    |History  of (string * MLast.ctyp * MLast.expr) list
    |Variable of (string * MLast.ctyp * MLast.expr) list

type strategy = Strategy of tactic
and tactic =
    |TaBasic  of string
    |TaModule of string * string
    |TaSkip
    |TaFail
    |TaSeq     of tactic * tactic
    |TaAlt     of tactic * tactic * MLast.expr
    |TaFairAlt of tactic * tactic * MLast.expr
    |TaAltCut  of tactic * tactic
    |TaMu   of string * tactic
    |TaVar  of string
    |TaMVar of string

type tableau = Tableau of rule list
and rule = Rule of
    (string *
    ruletype *
    numerator *
    (denominator list * branchcond) *
    condition list *
    action list list *
    condition list list *
    backtrack list *
    cache option *
    heuristic option )

and ruletype    = ExChoice | UnChoice | Choice | NoChoice
and numerator   = Numerator   of numcont array
and denominator = Denominator of dencont array | Status of string

and numcont = (arity * pa_expr) list
and arity = Single | Empty | Set
and dencont = ex_expr list
and label = string

and pa_expr =
    |PaTerm of pa_term
    |PaLabt of (label * MLast.patt) * pa_term
    |PaTupl of pa_expr list
    |PaPatt of MLast.patt

and ex_expr =
    |ExAppl of Stdpp.location * string * ex_expr
    |ExLabt of Stdpp.location * (label * MLast.expr) * ex_term
    |ExTerm of Stdpp.location * ex_term
    |ExTupl of Stdpp.location * ex_expr list
    |ExExpr of Stdpp.location * MLast.expr

and ex_term =
    |ExConn  of string * ex_term list
    |ExCons  of string
    |ExAtom  of string
    |ExVar   of string
    |ExHist  of string
    |ExVari  of string * varindex

and pa_term =
    |PaConn of label * string * pa_term list
    |PaCons of label * string
    |PaAtom of label * string
    |PaVar  of label * string
    |PaHist of string
    |PaVari of string * varindex
 
and varindex  = Int of int | All | Last | Null
and condition = Condition of ex_expr
and branchcond = ForAll | Exists | User | Linear
and action    =
    |Assign of ex_term * ex_expr
    |Function of ex_expr
and backtrack = action
and cache = MLast.expr
and heuristic = MLast.expr
