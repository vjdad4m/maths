# Kelmans: prescribed adjacent-pair deletion plus one edge can fail

Lean verifies a 14-vertex simple cubic graph that is 3-vertex-connected
and cyclically four-edge-connected. Remove the ends of the prescribed
edge 4–8 and also remove the disjoint prescribed edge 9–10. The
remaining graph has no partition into three-vertex paths.

The endpoints 9 and 10 become leaves. Their tiles must use 12 and 6,
respectively. The four ways to complete these two tiles leave an
isolated vertex either immediately or after a forced third tile.

This refutes the stronger auxiliary rule that asks to delete an
arbitrarily prescribed adjacent pair and simultaneously avoid an
arbitrary additional edge. It does not refute ordinary adjacent-pair
deletion, a rule allowing a choice of neighbor, or Kelmans's conjecture.

See `T2AvoidCounterexample.no_factor_pair_and_edge` and
`T2AvoidCyclicFour.cyclic_four`. Use Lean 4.19.0 and Mathlib at
`c44e0c8ee63ca166450922a373c7409c5d26b00b` on `LEAN_PATH` and run
`bash kelmans-t2-one-edge-obstruction/replay.sh` from the repository root.
