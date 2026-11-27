# Kelmans F2: a different auxiliary wire for asymmetric faithful caps

Consider the exact enlarged theta layout, where the absorbed exterior
neighbor's two remaining wires may land at different exterior sites.
The revised three-vertex cap places its suppressed auxiliary wire at
the other neighbor of the absorbed live contact. The local cut
comparison allows coincident exterior labels.

Lean verifies exact factor lifting and, when the revised cubic cap
satisfies the required cyclic-four property, the reduction to smaller
F2. The 22-vertex cubic example has a verified nontrivial three-cut in
the former cap and a checked exact factor obtained via the revised
route. This package does not verify the full cut conditions of the
original or revised graphs in that example.

Main result: `ThetaAsymmetricFaithful.reduce_of_valid_cap`.
General cap validity in the asymmetric layout and the Kelmans
conjecture remain open.

Use Lean 4.19.0 and Mathlib at
`c44e0c8ee63ca166450922a373c7409c5d26b00b` on `LEAN_PATH`.
From repository root run `bash kelmans-theta-asymmetric-faithful/replay.sh`.
