# Pgeon

Pgeon (Prover GEneratiON) is a generic tableau prover for first order logic.

## Getting Started

To build Pgeon, install:
- OCaml (version >= 4.12)
- The [Dune OCaml build system](https://github.com/ocaml/dune/) (version >= 3.19)

Opam (https://opam.ocaml.org/) is the recommended way to install OCaml and the required packages.
```bash
git clone https://gite.lirmm.fr/rsidhoum/pgeon/
cd pgeon
opam switch create . 4.12.1
eval $(opam env)
opam install dune
```

## Usage

Build and run Pgeon with Dune:
```bash
eval $(opam env) # (only needed in a fresh shell)
dune exec pgeon -- examples/LK/fo/lk_fo.txt examples/LK/fo/drinker.txt
```

The first argument is a `.pgeon`-style logic specification and the second is a problem instance containing formulas to prove.

Use `--focused` to run the experimental branch-obligation interpreter with
phase-based rule scheduling:
```bash
dune exec pgeon -- --focused gore_3.txt GSY044+1.txt
```

This mode saturates invertible rules before exploring non-invertible choices,
memoizes canonical branches, and preserves syntactic post-phases declared as
`noninvertible-rule ; post-strategy`.

The two main search changes can also be tested independently:
```bash
# Branch obligations, with rule operations still selected by the strategy.
dune exec pgeon -- --branch-obligations gore_3.txt GSY044+1.txt

# Phase scheduling, while retaining one global proof tree.
dune exec pgeon -- --phase-scheduling gore_3.txt GSY044+1.txt
```

Passing both independent flags is equivalent to `--focused`.
