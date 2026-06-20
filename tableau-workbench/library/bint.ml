(* A version of Dragalin's GHPC for Bi-Intuitionistic Logic BiInt 

   A prover without histories but using variables for bi-intuitionistic 
   propositional logic where backward proof search terminates.

   Based upon:
   L Buisman and R Gore
   A cut-free sequent calculus for Bi-Intuitionistic Logic
   Proc. TABLEAUX 2007, LNCS ? : ?-?, Springer, 2007.
*)

CONNECTIVES [
"~";"!";"&";"v";"->";"-<";"<->";
">-<";"^";"+";"#";"^^";"++";"=>"] 
GRAMMAR
  formula :=
       ATOM | Verum | Falsum | Special
      | formula & formula
      | formula v formula
      | formula -> formula
      | formula <-> formula
      | formula -< formula     (* A -< is "A Excludes B" *)
      | formula >-< formula
      | formula ^^ formula
      | formula ^ formula
      | formula ++ formula
      | formula + formula
      | # formula 
      | ! formula              (* ! A is intuitionistic negation *)
      | ~ formula              (* ~ A is dual intuitionistic negation *)
  ;;

  expr := formula ;;
  node := set => set ;;      (* GHPC format so sets on both sides *)
END

open BintFunctions

VARIABLES
  s : FormulaSetSet.set := new FormulaSetSet.set ;
  p : FormulaSetSet.set := new FormulaSetSet.set
END

SEQUENT

  RULE Ret
           Open
         ========= 
          G => D

       BACKTRACK [  s := setset(G) ; p := setset(D) ]
  END

  RULE Id
               Close
         ==================
          { A } => { A }
       
       BACKTRACK [ s := emptysetset() ; p := emptysetset() ]
  END

  RULE False
               Close
         ==================
          { Falsum } =>

       BACKTRACK [ s := emptysetset() ; p := emptysetset() ]
  END

  RULE True
               Close
         =================
          => { Verum }

       BACKTRACK [s := emptysetset() ; p := emptysetset() ]
  END

  RULE NegIL
               ! X ; X -> Falsum ; G =>
              ============================
                   { ! X } ; G  => 

       COND      [ notin(X -> Falsum, G) ]
       BACKTRACK [ s := s@1 ; p := p@1   ]
  END

  RULE NegIR
               => ! Y ; Y -> Falsum ; D
              ==========================
               => { ! Y } ; D

       COND      [ notin(Y -> Falsum, D) ]
       BACKTRACK [ s := s@1 ; p := p@1   ]
  END

  RULE NegDL
            Verum -< X ; ~ X ; G=>
          ==========================
               { ~ X }  ; G => 

       COND      [ notin(Verum -< X,G) ]
       BACKTRACK [ s := s@1 ; p := p@1 ]
  END

  RULE NegDR
             => Verum -< Y ; D ; ~ Y
           ===========================
               => { ~ Y } ; D 

       COND      [ notin(Verum -< Y,D) ]
       BACKTRACK [ s := s@1 ; p := p@1 ]
  END

  RULE AndL
            G ; A & B ; A ; B =>
           =========================
            G ; { A & B } => 

       COND      [ disjnotin(A,B,G,G)  ]
       BACKTRACK [ s := s@1 ; p := p@1 ]
  END

  RULE AndR
            => A ; A & B ; D      |    => B ;  A & B ; D
            =================================================
                => { A & B } ; D

       COND      [ conjnotin(A,B,D,D) ]
       BACKTRACK [  s := union(s@1, s@2) ; p := union(p@1, p@2) ]
  END

  RULE OrL
            A ; A v B ; G => | B ; A v B ; G => 
           ==========================================
                   { A v B } ; G => 

       COND      [ conjnotin(A,B,G,G) ]
       BACKTRACK [  s := union(s@1, s@2) ; p := union(p@1, p@2) ]
  END

  RULE OrR
             => A ;  B ; A v B ; D
            =========================
             => { A v B } ; D

       COND      [ disjnotin(A,B,D,D)   ]
       BACKTRACK [  s := s@1 ; p := p@1 ]
  END

  RULE ImpL
             A -> B ; G =>  A ; D |   B ; A -> B ; G =>  D 
             ==================================================
                        { A -> B } ; G =>  D 

       COND [ conjnotin(A,B,D,G) ]
       BACKTRACK [  s := union(s@1, s@2) 
               ; p := union(p@1, p@2) 
       ]
  END

  RULE ExcR
             G =>  A ; D ; A -< B |   B ; G =>  D ; A -< B 
             ==================================================
                        G =>  D ; { A -< B }

       COND [ conjnotin(A,B,D,G) ]
       BACKTRACK [ s := union(s@1, s@2) 
                 ; p := union(p@1, p@2) 
       ]
  END

  RULE ImpR1
             => B ; A -> B ; D
            =====================
             => { A -> B } ; D 

       COND [ notin(B, D) ]
       BACKTRACK [ s := s@1
                 ; p := p@1
       ]
  END

  RULE ExcL1
             A ; A -< B ; G => 
            =======================
            { A -< B } ; G    =>  

       COND [ notin(A, G) ]
       BACKTRACK [ s := s@1
                 ; p := p@1
       ]
  END

  RULE ImpR2b
             A ; G => B  ||   G  => A -> B ; D ; bigand(p@1)
            ===========================================================
                      G => { #( A -> B) } ; D 

       BRANCH [ isnotemptyandallsubsnotsub(p@1, A -> B, D) ]
       BACKTRACK [ s := special(s@all, G , [ ]) 
              ; p := special(p@all, A -> B, D)
       ]
  END

  RULE ImpR2a
                      G => #(A -> B) ; D
                  -------------------------------
                      G => { A -> B } ; D 

       COND   [ notin(A,G) ]
       BRANCH [ parentisspecial(s@1, p@1) ]
       BACKTRACK [ s := compute(s@all, G, [])
              ; p := compute(p@all, A -> B, D )
       ]
  END

  RULE ExcL2b
              A => B ; D  |||   A -< B ; G ; bigor(s@1) => D 
            =========================================================
                { #(A -< B) } ; G => D

       BRANCH [ isnotemptyandallsubsnotsub(s@1, A -< B, G) ] 
       BACKTRACK [ s := special(s@all, A -< B, G)
                 ; p := special(p@all, D, [])
       ] 
  END

  RULE ExcL2a
                      #( A -< B ) ; G => D
                  ---------------------------
                      { A -< B } ; G => D

       COND   [ notin(B,D) ]
       BRANCH [ parentisspecial(s@1, p@1) ] 
       BACKTRACK [ s := compute(s@all, A -< B, G)
                 ; p := compute(p@all, D, [])
       ]

  END

  RULE BigOrL
                unconjoin(A) =>    |       B => 
            =============================================
                         {A + B}  => 

       BACKTRACK [ s := union(s@1, s@2) 
                 ; p := union(p@1, p@2) 
       ]
  END

  RULE BigAndR
                => undisjoin(A)  |          => B
            =============================================
                         => {A ^ B}
       BACKTRACK [ s := union(s@1, s@2) 
                 ; p := union(p@1, p@2) 
       ]
  END

END


let exit = function
    |"Open" -> "Not Derivable"
    |"Close" -> "Derivable"
    |s -> assert(false)

EXIT := exit(status@1)

STRATEGY := 
 let 
     saturate = tactic (     Id    
                           ! False ! True
                           ! NegIL ! NegIR
                           ! NegDL ! NegDR
                           ! AndL  ! OrR
                           ! ImpR1 ! ExcL1
                           ! OrL   ! AndR  
                           ! ImpL  ! ExcR
                           ! BigAndR ! BigOrL )
 in
 let impjump     = tactic (ImpR2a ; ImpR2b) in
 let excjump     = tactic (ExcL2a ; ExcL2b) in 
 tactic ( (saturate ! ( impjump ||  excjump ) )* ; Ret ) 

MAIN
