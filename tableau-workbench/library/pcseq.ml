
CONNECTIVES [ "~";"&";"v";"->";"<->";"=>" ]
GRAMMAR
formula :=
     Atom | Verum | Falsum
    | formula & formula
    | formula v formula
    | formula -> formula
    | formula <-> formula
    | ~ formula
;;

expr := formula ;;
node := set => singleton ;;
END

SEQUENT

  RULE Id
  Open
  ============== 
  { a } => { a }
  END

  RULE AndL
  A ; B => 
  ============
  { A & B } => 
  END

  RULE AndR
  => A | => B
  ============
  => { A & B } 
  END

  RULE OrL
  A => | B => 
  ============
  { A v B } => 
  END

  RULE OrR
  => A ; B
  ============
  => { A v B } 
  END

END

STRATEGY := tactic ( (Id|AndL|AndR|OrL|OrR)* )

MAIN

