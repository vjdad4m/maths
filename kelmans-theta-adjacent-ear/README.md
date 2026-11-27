# Kelmans F2: absorbing one adjacent theta contact pair

Lean checks the exact seven-vertex theta attachment in both orientations.
The ambient graph is cubic with the stated cyclic-four and cyclic-five cut
properties, order four modulo six, and five distinct ports. If an opposite
pair of exterior contacts is adjacent, absorb its two vertices. The result
applies when the two specified replacement pairs in the released exterior
are nonadjacent. It handles any genuine omitted exterior edge **other than
the absorbed pair**, including an edge that touches an absorbed endpoint.

The smaller cap has six fewer vertices. Under the explicit hypothesis of
smaller-order cyclic-four F2, delete its midpoint and omit either the same
edge (if retained) or its corresponding replacement wire. The transfer
checks all nine ways the two live cap leaves can occur in the factor and
restores the original graph without using the requested omitted edge.
Theorems: `ThetaAdjacentEarOriginal.original_from_adjacent` and
`ThetaAdjacentEarMirror.mirrored_original_from_adjacent`.

The replacement-pair hypotheses are essential to this particular routing.
The package also checks a cubic, cyclic-five, square-free 16-vertex
fixture with both replacement pairs adjacent and a nontrivial three-edge
cut in its prescribed cap. The original target still has the desired
factor. This is a limitation of the cap choice, not a counterexample to F2.
The full Kelmans conjecture remains open.

Use Lean 4.19.0 and Mathlib at `c44e0c8ee63ca166450922a373c7409c5d26b00b`
on `LEAN_PATH`. From the repository root, run
`bash kelmans-theta-adjacent-ear/replay.sh`.
