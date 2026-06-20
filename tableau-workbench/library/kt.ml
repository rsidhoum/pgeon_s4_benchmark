
source K

module FormulaSet = TwbSet.Make(
    struct
        type t = formula
        let to_string = formula_printer
        let copy s = s
    end
)

HISTORIES
BOXES    : FormulaSet.set := new FormulaSet.set
END

open Twblib
open Klib

TABLEAU

  RULE T
  { [] A }
  =========
  A ; [] A

  COND notin(A, BOXES)

  ACTION [ BOXES := add(A,BOXES) ]
  END
 
  RULE K
  { <> A } ; [] X ;  Z
  ----------------------
          A ; X
  ACTION [ BOXES := clear(BOXES) ]
  END

  RULE Id { a } ; { ~ a } === Close END
  RULE False Falsum === Close END
  RULE And { A & B } === A ; B END
  RULE Or { A v B } === A | B END

END


STRATEGY :=
    let sat = tactic ( (Id ! False ! And ! Or ! T) ) in
    tactic ( ((sat)* ; K )* )

PP := List.map nnf
NEG := List.map neg

MAIN

