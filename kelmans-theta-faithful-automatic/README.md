# Kelmans F2: automatic validity in the faithful seven-wire layout

In the exact cubic seven-wire faithful theta layout, with ambient
cyclic-five cut condition and order four modulo six, the designated
three-vertex cap is automatically cyclically four-edge-connected.
No separate cap or port-group test is needed.

The proof shows that forbidden port edges would create a small
ambient cut with nontrivial shores, or a forbidden triangle. The
[exact cap-validity criterion](../kelmans-theta-faithful-cap-validity/)
then gives the cut condition. The resulting exact edge-and-root
omission reduces to smaller cyclic-four F2 on six fewer vertices.

Main theorem: `ThetaSevenFaithfulAutomatic.reduce_automatic`.
The precise layout still matters: the absorbed exterior neighbor
must have the prescribed two heavy-contact incidences. Other
placements and general F2 and Kelmans remain open.

Use Lean 4.19.0 and Mathlib at
`c44e0c8ee63ca166450922a373c7409c5d26b00b` on `LEAN_PATH`.
From repository root run `bash kelmans-theta-faithful-automatic/replay.sh`.
