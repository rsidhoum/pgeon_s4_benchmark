
define PROJ_sequent
  USE_CAMLP4 = yes
  SOURCES := ast.ml entrylib.ml keywords.ml parselib.ml syntaxChecker.ml extGramm.ml tablib.ml extCommon.ml
  RESULT := pa_sequent
  export PACKS := str unix twb.types
endef
export PROJ_sequent

define PROJ_input
  USE_CAMLP4 = yes
  SOURCES := ast.ml entrylib.ml inputParser.ml
  RESULT := inputParser
  export PACKS := str unix camlp5.gramlib
endef
export PROJ_input

ifndef SUBPROJS
  export SUBPROJS = sequent
endif

all: bcl inputncl

inputncl:
	@$(MAKE) -f $(OCAMLMAKEFILE) subprojs SUBTARGET=ncl SUBPROJS=input OCAMLFLAGS=

# Catch-all target will be applied to all subprojects automatically
%:
	@$(MAKE) -f $(OCAMLMAKEFILE) subprojs SUBTARGET=$@ OCAMLFLAGS=
