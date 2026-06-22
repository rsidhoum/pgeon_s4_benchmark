# S4 Benchmark

This repository builds and compares Pgeon and Tableau Workbench on S4 modal
logic problems. The input problems are QMLTP/TPTP files in `problems/*.p`.
The local parser translates each input file to both solver formats:

- `problems/pgeon/*.pgeon`
- `problems/twb/*.twb`

The benchmark then runs both solvers and writes `results.csv`.

## TLDR

```sh
make && make bench
```

## Projects

Pgeon is based on the commit `58cae0632f3ed75527a644678cd875858a787f62` at <https://gite.lirmm.fr/rsidhoum/pgeon.git>.

Tableau Workbench is based on the commit `e0214f7fb2ae209418fcaa0a53083c52d139f07b` at <https://github.com/rsidhoum/tableau-workbench>.

## Requirements

Install `opam` first. The build uses a local opam switch in `_opam` and pins
the shared OCaml toolchain for all components:

- OCaml `4.12.1`
- Dune `3.19.0`
- Camlp5 `7.14`
- `ocamlfind`
- `extlib`
- `menhir`

## Build

Create the local switch and install dependencies:

```sh
make setup
```

## Benchmark

Run the benchmark:

```sh
make bench
```

This creates `results.csv` and prints a per-problem summary. Pgeon and Tableau
Workbench results are shown in green when they match the expected result and in
red otherwise. The CSV columns are:

- `file`: problem basename
- `expected_status`: status read from the original QMLTP/TPTP problem
- `expected_result`: accepted solver result for the emitted problem
- `pgeon_result`, `pgeon_time`, `pgeon_ok`
- `twb_result`, `twb_time`, `twb_ok`
- `same`: whether Pgeon and Tableau Workbench returned the same result

Statuses are mapped as follows:

| QMLTP/TPTP status | Expected solver result |
| --- | --- |
| `Theorem` | `Close` |
| `Unsatisfiable` | `Close` |
| `NonTheorem` | `Open/Close` |
| `Satisfiable` | `Open` |

For conjecture problems labelled `Theorem`, the parser translates the benchmark
as a refutation task: axioms are kept and the conjecture is negated. Other
conjectures are emitted unchanged. Therefore theorem and unsatisfiable problems
are expected to close, satisfiable problems are expected to remain open, and
non-theorem problems accept either result: `Close` means the non-negated formula
is unsatisfiable, while `Open` means it is satisfiable but not valid.

## Problems

Put source problems (in TPTP or QLMTP format) directly in `problems/`.

## Cleaning

Remove build outputs and generated problem translations:

```sh
make clean
```

Remove the local opam switch and dependency stamp as well:

```sh
make distclean
```
