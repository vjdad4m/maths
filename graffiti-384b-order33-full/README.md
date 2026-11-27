# Graffiti.pc #384b: the complete order-33, 32-nonleaf profile

A finite simple graph on 33 vertices with exactly 32 vertices of degree at least two and exactly 31 distinct vertex triangle-incidence counts has a 2-dominating set of size at most 17. No connectedness assumption is needed. [Combined theorem](src/OrderThirtyThree384b.lean)

The [shared-neighbor and no-leaf proof](src/NoLeafAttachment.lean) forces a degree-two vertex adjacent to a leaf in any hypothetical failure. The [adjacent degree-two proof](../graffiti-384b-adjacent-full/src/CompleteAdjacent.lean) forces the degree-two vertices to be pairwise nonadjacent in a failure. The [leaf-adjacent proof](../graffiti-384b-leaf-full/src/LeafFinish.lean) then gives the required bound. This profile is settled, not the full conjecture.

Run `bash replay.sh` with `CROSSFOUR_LEAN_BIN` and `CROSSFOUR_MATHLIB` pointing to Lean 4.19.0 and the built pinned Mathlib checkout. It rebuilds the published thirteen-contact baseline and checks the exact sources of the subsequent packages before compiling the integration theorem. The proof uses only standard Lean axioms.
