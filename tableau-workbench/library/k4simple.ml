
source K

module FormulaSet = TwbSet.Make(
    struct
        type t = formula
        let to_string = formula_printer 
        let copy s = s
    end
)

HISTORIES
  LOOP : FormulaSet.set := new FormulaSet.set
END

open Twblib
open Klib

let loopcheck(a,b,h) = notin(a@b,h)
let addloop(a,b,h) = add(a@b,h)

TABLEAU

  RULE K4
  { <> A } ; [] X ; Z 
  ------------------ 
  A ; [] X ; X

  COND loopcheck(<> A, [] X, LOOP)
  ACTION [ LOOP := addloop(<> A, [] X, LOOP) ]
  END

  RULE Id { a } ; { ~ a } === Close END
  RULE False Falsum === Close END
  RULE And { A & B } === A ; B END
  RULE Or { A v B } === A | B END
  
END

STRATEGY := 
    let sat = tactic ( (False ! Id ! And ! Or) )
    in tactic ( (sat ! K4 )* )

PP := List.map nnf
NEG := List.map neg

MAIN
