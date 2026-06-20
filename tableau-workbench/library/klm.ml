(* This is a prover for KLM logic P as defined in the work of
   L Gordano, V Gliozzi, N Olivetti, G Pozzato
   "Analytic tableaux for KLM Preferential and Cummulative Logic"
   Proceedings of LPAR 2005 LNAI 3835:666-681, Springer, 2005.
*)


CONNECTIVES [ "~" ; "&" ; "v" ; "->" ; "<->" ; "<>" ; "[]"
              ; "=>"  (* Conditional Implication *)
]

GRAMMAR

formula :=  ATOM | Verum | Falsum
         | formula => formula
         | formula & formula
         | formula v formula
         | formula -> formula
         | formula <-> formula
         | [] formula
         | <> formula
         | ~ formula
;;

expr := formula ;;
END


module FormulaSet = TwbSet.Make(
    struct
        type t = formula
        let to_string = formula_printer
        let copy s = s
    end
)

HISTORIES
  CIMPS : FormulaSet.set := new FormulaSet.set
END

open Twblib
let nnfl = List.map Klmlib.nnf

TABLEAU

  RULE CImpp { A => B }   == nnfl( ~ A ) | <> A  | nnfl( B )

       ACTION [ [ CIMPS  := add(A => B, CIMPS) ] ;
                [ CIMPS  := add(A => B, CIMPS) ] ;
                [ CIMPS  := add(A => B, CIMPS) ]
       ]
  END

  RULE False { Falsum }       == Close  END
  RULE Id    { A } ; { ~ A }  == Close  END     (* formulae not atoms! *)
  RULE And     X & Y          == X ; Y  END
  RULE Or    { A v B }        == A | B  END


(* The following two rules are non-invertible                 *)
(* So they need some sort of special trick to make then work  *)
(* under the current TWB                                      *)

(*
   It is imperative to never jump on the same <> A twice to
   maintain the well-foundedness of the underlying transitive
   relation. We achieve this by storing [] ~ <> A in the
   denominator. From now on, every <> jump will bring out the
   ~ <> A. So if <> A ever turns up again (ID) will close the
   branch before jumping on <> A again.
*)

  RULE CImpm { ~ ( A => B ) } ; ~ ( X => Y ) ; Z
             -------------------------------------------------------------------------------
             nnfl(A) ; ~ <> A ; [] ~ <> A  ;  nnfl( ~ <> A) ; nnfl(~ B) ; ~ (X => Y) ; CIMPS
  END


  RULE K     { <> A } ; ~ (X => Y) ; [] W ; Z
             -------------------------------------------------------------------------------
             nnfl(A) ; ~ <> A ; [] ~ <>  A ;  nnfl( ~ <> A) ; ~ (X => Y) ; W ; [] W ; CIMPS
  END
END

PP := nnfl
NEG := List.map Klmlib.neg

let saturate = tactic (False ! Id ! And ! Or ! CImpp)
STRATEGY tactic ( (saturate ! (CImpm || K) )* )

MAIN

