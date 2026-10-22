# Circular coloring counterexample

Author: Alex Chan, Harvard University and National Bureau of Economic Research.

This repository formalizes two finite statements about
K_(5/2) OR K_(11/4), with vertex set Fin 5 × Fin 11:

- No (33,4)-coloring exists.
- The supplied table is a valid (17,2)-coloring.

The obstruction theorem is `CircularColoring.no_coloring33_4`.
The upper-bound certificate is checked by `witness_in_range` and
`witness_respects_edges` in `CircularColoring/Witness.lean`.

## Verification

The Lean toolchain is pinned in `lean-toolchain`. Mathlib is pinned
in `lakefile.toml` and `lake-manifest.json`.

After installing elan, run:

```sh
lake exe cache get
lake build
python3 scripts/check_axioms.py
```

The audit permits only `propext`, `Classical.choice`, and `Quot.sound`.
It checks the transitive axiom dependencies of the main obstruction
and the other declarations printed by `Audit.lean`.

## Scope

The formalization proves the fixed finite obstruction and verifies
the explicit upper-bound coloring. It does not formalize the paper's
infinite family or a general theory of circular chromatic numbers.
The interpretation of the finite obstruction as a strict circular
chromatic lower bound uses standard results discussed in the paper.

Repository: https://github.com/alexgocardinal/liu-zhu-circular-coloring

## Manuscript

[Paper PDF](paper/paper.pdf) · [LaTeX source](paper/paper.tex)

Compile the manuscript with Tectonic:

```sh
tectonic --outdir paper paper/paper.tex
```
