# Circular coloring counterexample

Alex Chan, Harvard University and National Bureau of Economic Research.

This repository formally disproves the Liu–Zhu circular-coloring
inequality using K_(5/2) OR K_(11/4).

## Main results

- `CircularColoring.liu_zhu_counterexample` proves that the
  Liu–Zhu inequality fails for these two factors.
- `CircularColoring.liu_zhu_strict_counterexample` states the
  strict inequality between the proposed bound and the product's
  circular chromatic number.
- `CircularColoring.counterexample_circular_bounds` proves
  33/4 < chi_c(X) <= 17/2.

The formalization includes the graph definitions, the finite
obstruction, rounding of real colors, attainment of the minimum
circumference, the explicit upper-bound coloring, and ordinary
3-colorings of the factors. Ordinary chromatic numbers use Mathlib's
definition. Circular chromatic numbers are defined as infima of
feasible real circle circumferences.

## Verification

Lean and Mathlib are pinned to version 4.35.0.

```sh
lake exe cache get
lake build
python3 scripts/check_axioms.py
```

The audit permits only `propext`, `Classical.choice`, and `Quot.sound`
and checks the transitive dependencies of the final counterexample.

## Scope

The fixed 55-vertex counterexample is formalized. The paper's
infinite-family theorem and additional corollaries are not included
in this formal verification.

## Manuscript

[Paper PDF](paper/paper.pdf) · [LaTeX source](paper/paper.tex)

```sh
tectonic --outdir paper paper/paper.tex
```

Repository: https://github.com/alexgocardinal/liu-zhu-circular-coloring
