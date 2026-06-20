
USE_CAMLP4 = yes
SOURCES := \
	../timer.ml \
	twbCli.ml
RESULT := twbcli
export PACKS := twb

OCAMLDOC := ocamlfind ocamldoc -package $(PACKS)
DOC_FILES := $(SOURCES)

all: ncl

include $(OCAMLMAKEFILE)

