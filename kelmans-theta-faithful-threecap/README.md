# Kelmans F2: a faithful three-vertex cap for an enlarged theta

This is an exact smaller-F2-only reduction in the seven-wire layout
that results from absorbing one live theta contact and its exterior
neighbor. Their genuine connecting edge is the requested omission.

In the cap, two linked new vertices encode the live and deleted ends,
while the third is a faithful copy of the absorbed exterior neighbor.
When the specified cap is cyclically four-edge-connected, smaller F2
on six fewer vertices supplies the input. Lean verifies that every
possible tiling at the live cap vertex lifts without the original
omitted edge, even when its tile contains the faithful vertex.

The exact theorem is `ThetaSevenFaithfulCap.reduce`. The package also
checks a concrete cubic 16-vertex theta with both opposite pairs absent:
its ten-vertex cap satisfies the required cut condition, and Lean
lifts an explicit cap factor to a factor omitting the original edge
7–13. The general availability of such a cap, other omission types,
and the Kelmans conjecture remain open.

Use Lean 4.19.0 and Mathlib at
`c44e0c8ee63ca166450922a373c7409c5d26b00b` on `LEAN_PATH`.
From repository root run `bash kelmans-theta-faithful-threecap/replay.sh`.
