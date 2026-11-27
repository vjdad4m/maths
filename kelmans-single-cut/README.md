# Reducing a Kelmans graph with one cyclic three-edge cut

**This is a conditional reduction to the cyclically 4-edge-connected class, not an unconditional (P_3)-factor theorem.**

Assume every finite simple cubic 3-vertex-connected graph of order divisible by six and cyclic edge-connectivity at least four has a (P_3)-factor. Then a finite simple cubic 3-vertex-connected graph of order divisible by six with exactly one nontrivial three-edge cut also has a (P_3)-factor. A cut is counted without distinguishing which shore is named first. The exact statement is [`cyclic4_factor_implies_single_three_cut`](src/SingleThreeCut.lean).

The proof works more generally if there are two vertex-disjoint edges such that, for every nontrivial three-edge cut, the two edges lie wholly within opposite shores. Pick an internal edge of each shore for the single-cut case. Subdivide those edges once each and join the new vertices. Any small cut in the resulting cubic graph projects to a cut in the original graph with no more crossings. A projected nontrivial three-edge cut must cross at least one additional edge of the handle, whichever sides contain the new vertices. If the projected cut is trivial, the standard [handle argument](../kelmans-handle) shows that a cut of size at most three in the larger graph is still trivial.

The new graph is thus in the cyclic-4 class and has order two modulo six. Apply [adjacent-pair deletion](../kelmans-affine-t2) to the two new vertices. The resulting factor uses neither original edge and is also a factor of the original graph. [HandleHitting.lean](src/HandleHitting.lean) checks the exact crossing hypothesis and the factor transfer.

Lean also verifies a limitation of this method: three pairwise disjoint nontrivial shores of small cuts cannot all contain one of the two selected edges, so no single handle can meet the required crossing condition. This is not a counterexample to the conjecture.

## Replay

From a Lean 4.19.0 project with the Mathlib 4.19.0 build cache:

    lake env bash /path/to/maths/kelmans-single-cut/replay.sh
