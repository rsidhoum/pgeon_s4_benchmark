
USE_CAMLP4 = yes
SOURCES := \
        ../timer.ml \
        twbCgi.ml
RESULT := twbcgi
export PACKS := twb xmlrpc-light

OCAMLDOC := ocamlfind ocamldoc -package $(PACKS)
DOC_FILES := $(SOURCES)

all: ncl

include $(OCAMLMAKEFILE)

