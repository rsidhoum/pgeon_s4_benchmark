# TPTPTPTP : TPTP Translation Parser for Tableaux and PGeon

Translates problem files from TPTP and QMLTP to PGeon and Tableau Workbench problem files.

### Supported
- PGeon (--pgeon)
- Tableaux Workbench (--twb)

### Requierements
- Dune
- Menhir
- OCamllex

### Usage
dune exec parser -- --<options> <problem_file_path> [> <output_file>]
