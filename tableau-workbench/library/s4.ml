
source K

module FormulaSet = TwbSet.Make(
    struct
        type t = formula
        let to_string = formula_printer 
        let copy s = s
    end
)

HISTORIES
  DIAMONDS : FormulaSet.set := new FormulaSet.set;
  BOXES    : FormulaSet.set := new FormulaSet.set
END

open Twblib
open Klib

TABLEAU

  RULE S4
  { <> A } ; Z --- A ; BOXES
  COND notin(<> A, DIAMONDS)
  ACTION [ DIAMONDS := add(<> A,DIAMONDS) ]
  END

  RULE T
  { [] A } === A
  COND notin(A, BOXES)
  ACTION [
      BOXES    := add(A,BOXES);
      DIAMONDS := emptyset(DIAMONDS)]
  END

  RULE Id { a } ; { ~ a } === Close END
  RULE False Falsum === Close END
  RULE And { A & B } === A ; B END
  RULE Or { A v B } === A | B END
  
END

STRATEGY := 
    let sat = tactic ( (False ! Id ! And ! T ! Or) )
    in tactic ( (sat ! S4 )* )

PP := List.map nnf
NEG := List.map neg

MAIN

(*
  RULE S4H
  { <> A } ; <> Y ; Z 
  ======================
   A ; BOXES || <> Y

  COND notin(<> A, DIAMONDS)
  ACTION [
      [ DIAMONDS := add(<> A,DIAMONDS);
        DIAMONDS := add(<> Y,DIAMONDS)]
  ]
  BRANCH not_emptylist(<> Y)
  END
*)
