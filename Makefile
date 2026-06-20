OPAM := opam
SWITCH := $(CURDIR)
OPAM_EXEC := $(OPAM) exec --switch=$(SWITCH) --
SWITCH_CONFIG := _opam/.opam-switch/switch-config
DEPS_STAMP := .deps-installed
OPAM_PACKAGES := ocaml-base-compiler.4.12.1 dune.3.19.0 ocamlfind extlib camlp5.7.14 menhir
PGEON_EXEC := ./pgeon/_build/install/default/bin/pgeon
TWB_EXEC := ./tableau-workbench/library/s4.twb
PARSER_EXEC := ./tptp2pgeon_parser/_build/install/default/bin/tptp2pgeon_parser
PGEON_STAMP := ./pgeon/_build/.s4_benchmark_build
TWB_STAMP := ./tableau-workbench/.s4_benchmark_build
PARSER_STAMP := ./tptp2pgeon_parser/_build/.s4_benchmark_build
PGEON_LOGIC := ./pgeon/gore_3.txt
PROBLEM_SOURCES := $(wildcard problems/*.p)
PGEON_PROBLEMS := $(patsubst problems/%.p,problems/pgeon/%.pgeon,$(PROBLEM_SOURCES))
TWB_PROBLEMS := $(patsubst problems/%.p,problems/twb/%.twb,$(PROBLEM_SOURCES))
GENERATED_PROBLEMS := $(PGEON_PROBLEMS) $(TWB_PROBLEMS)
PGEON_SOURCES := $(shell find pgeon -path 'pgeon/_build' -prune -o -type f \( -name '*.ml' -o -name '*.mli' -o -name 'dune' -o -name 'dune-project' \) -print)
PARSER_SOURCES := $(shell find tptp2pgeon_parser -path 'tptp2pgeon_parser/_build' -prune -o -type f \( -name '*.ml' -o -name '*.mli' -o -name '*.mll' -o -name '*.mly' -o -name 'dune' -o -name 'dune-project' -o -name '*.opam' \) -print)
TWB_SOURCES := $(shell find tableau-workbench -type f \( -name '*.ml' -o -name 'Makefile' -o -name 'Makefile.in' -o -name 'configure' -o -name 'configure.in' -o -name 'META' \) -print)

all: pgeon twb parser problems

bench: results.csv pretty_results.awk
	@COLOR=$$(test -t 1 && [ -z "$$NO_COLOR" ] && printf yes || printf no) awk -f pretty_results.awk results.csv

setup: $(DEPS_STAMP)

$(SWITCH_CONFIG):
	$(OPAM) switch create . --empty --yes

$(DEPS_STAMP): s4-benchmark.opam | $(SWITCH_CONFIG)
	$(OPAM) install --switch=$(SWITCH) $(OPAM_PACKAGES) --yes
	touch $@

pgeon: $(PGEON_STAMP)

$(PGEON_STAMP): $(DEPS_STAMP) $(PGEON_SOURCES)
	cd pgeon && $(OPAM_EXEC) dune build @install
	touch $@

twb: $(TWB_STAMP)

$(TWB_STAMP): $(DEPS_STAMP) $(TWB_SOURCES)
	cd tableau-workbench && $(OPAM_EXEC) ./configure
	$(MAKE) -C tableau-workbench
	$(MAKE) -C tableau-workbench provers
	touch $@

parser: $(PARSER_STAMP)

$(PARSER_STAMP): $(DEPS_STAMP) $(PARSER_SOURCES)
	cd tptp2pgeon_parser && $(OPAM_EXEC) dune build @install
	touch $@

problems/pgeon/%.pgeon: problems/%.p $(PARSER_STAMP)
	mkdir -p problems/pgeon
	$(OPAM_EXEC) $(PARSER_EXEC) --pgeon $< > $@

problems/twb/%.twb: problems/%.p $(PARSER_STAMP)
	mkdir -p problems/twb
	$(OPAM_EXEC) $(PARSER_EXEC) --twb $< > $@

problems: $(GENERATED_PROBLEMS)

results.csv: $(PGEON_STAMP) $(TWB_STAMP) $(GENERATED_PROBLEMS) benchmark.sh
	PGEON_LOGIC=$(PGEON_LOGIC) bash benchmark.sh > results.csv

clean:
	cd pgeon && $(OPAM_EXEC) dune clean
	cd tptp2pgeon_parser && $(OPAM_EXEC) dune clean
	if [ -f tableau-workbench/Makefile ]; then \
		$(MAKE) -C tableau-workbench clean; \
	fi
	rm -f $(GENERATED_PROBLEMS)
	rm -f $(PGEON_STAMP) $(TWB_STAMP) $(PARSER_STAMP)

distclean: clean
	if [ -f tableau-workbench/Makefile ]; then \
		$(MAKE) -C tableau-workbench dist-clean; \
	fi
	rm -f $(DEPS_STAMP)
	rm -rf _opam
	rm -f results.csv

.PHONY: all bench setup pgeon twb parser problems clean distclean
