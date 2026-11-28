# Graffiti.pc #189: connectivity two, order sixteen, degree-six threshold

The final exact Lean declaration is
`Graffiti189LongestPath.CrossSaturation.ThresholdSix.traceable_at_six_actual_two_cut_order_sixteen`.
It produces a spanning path in a 16-vertex finite simple graph when:

- the graph is connected and every singleton deletion remains connected;
- all but at most one vertex have degree at least six;
- each vertex has at most seven vertices at even shortest-path distance,
  counting itself;
- some two distinct vertices disconnect the graph when deleted.

The separator can be adjacent or nonadjacent. The first module also closes the
whole adjacent singleton+13 branch without hypotheses on visible-port or
balanced-dark counts. These are order-16 connectivity-two results, not
a proof of all threshold-six cases or of the full conjecture.

The separator leaves exactly two components under the hypotheses. Nonadjacent
cuts and pairs of nonsingleton shores are covered by the pinned predecessor
results. In the remaining adjacent case the components have orders one and
thirteen. Exact parity profiles leave only five or six visible ports on the
larger shore, and the corresponding checked predecessor theorem supplies a
spanning path in each case.

## Replay

Lean 4.19.0 with Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`.
Compile the objects listed in `PRIOR-MODULES.tsv` and their respective
dependencies, place their output directories in `LEAN_PATH`, and run
`./replay.sh`. The attached strict replay shows the two new modules and
the exact theorem axiom audits.
