# Exactly when one handle removes all small cyclic cuts

Let (G) be a finite simple cubic 3-vertex-connected graph. Pick two vertex-disjoint edges, subdivide each, and join the two new vertices. There is a choice of edges for which this handle operation yields a cyclically 4-edge-connected graph **if and only if** (G) has no three pairwise disjoint shores of nontrivial three-edge cuts. Here a nontrivial cut has at least two vertices on each side.

As a consequence, **if the Kelmans packing claim holds in the cyclically 4-edge-connected class, it holds for all cubic 3-vertex-connected graphs of order divisible by six with no such triple of disjoint shores**. This extends the [single-cut reduction](../kelmans-single-cut) and does not cover graphs with three pairwise disjoint shores. The structural characterization is unconditional; the packing conclusion is conditional.

The exact Lean statements are [`exists_cyclic_handle_iff_no_three_disjoint` and `cyclic4_factor_implies_no_three_disjoint_shores`](src/OneHandleExact.lean).

## Why it works

1. Cubicity and 3-vertex-connectivity give a lower bound of three on every proper edge cut. Two cuts of size three cannot cross. If all four intersections of their shores were nonempty, the two cut-sum identities force both diagonally opposite zone pairs to have no edges between them; each zone then has boundary three. The remaining four edge counts would force the original cut sizes to be even.
2. Consequently, inclusion-minimal nontrivial three-cut shores are pairwise disjoint, when both orientations are included. If two minimal shores overlapped without containment, the no-crossing property would force their union to be the whole graph; then the complement of one would be a proper qualifying subshore of the other. Every nontrivial shore contains a minimal one.
3. In the absence of a disjoint triple there are exactly two minimal shores, unless no nontrivial cuts exist. Each cut places these two on opposite sides. Choose one internal edge within each minimal shore. The handle crosses every nontrivial small cut. When there are no such cuts, any two disjoint edges suffice.
4. Conversely, if a nontrivial three-edge cut does not place the two selected edges wholly in opposite shores, there is a placement of the two new vertices extending the old cut with no extra crossings. Such a cut survives. Three disjoint nontrivial shores cannot all be met by two edges selected to lie internally in the required shores.

The [adjacent-pair deletion result](../kelmans-affine-t2) gives the conditional packing conclusion by deleting the handle endpoints, then restoring the original two edges.

## Replay

From a Lean 4.19.0 project with the Mathlib 4.19.0 build cache:

    lake env bash /path/to/maths/kelmans-one-handle/replay.sh
