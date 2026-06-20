
source K

open Twblib
open Klib
open Kopt

let simpl(a,b) =
    let b = nnf(List.hd b) in (* must be a single formula *)
    List.map (fun x -> simpl nnf b x) a
;;

TABLEAU

  RULE K
  { <> A } ; [] X ; Z
  ----------------------
    A ; simpl(X,A)

  END

  RULE Id
  { a } ; { ~ a }
  ===============
    Close
  END

  RULE False
  { Falsum }
  =========
    Close
  END

  RULE And
  { A & B } ; X
  ==============
      simpl(A,B) ; simpl(B,A) ; simpl(simpl(X,A),B)
  END
  
  RULE Or
  { A v B } ; X
 =================================
     A ; simpl(X,A) | simpl(B, ~ A) ; simpl(simpl(X,B),~ A)
  END

END

PP := List.map nnf
NEG := List.map neg

let saturate = tactic ( False!Id!And!Or )

STRATEGY := tactic ( ( saturate ! K )* )
MAIN
