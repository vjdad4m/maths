# Graffiti.pc #133: a dominating 7-cycle with triangle-free singleton exterior

Lean verifies the following subcase. Let the graph be finite with no
ordinary 4-cycle and no induced 9-vertex path. Suppose it has an induced
7-cycle such that every outside vertex has exactly one neighbor on the
cycle, and there are no triangles wholly outside the cycle. Then

1. Every induced graph on a subset of the exterior has at most as many
   edges as vertices.
2. The mean local independence number of the whole graph is at most four.

For the first assertion, a minimum induced subgraph with more edges than
vertices must have all degrees two except either one degree-four vertex
or two degree-three vertices. The checked decomposition gives a
figure-eight, theta, or dumbbell, with restricted path lengths. The
[19-motif certificates](../graffiti-133-bicycle-motifs/) produce an induced
9-vertex path in the host graph. This contradicts the hypothesis. The
second assertion follows by summing local independence and using the
exterior degree sum.

The exact theorems are `singleton_seven_exterior_edges` and
`singleton_triangle_free_seven_mean_four` in `src/BicycleSingletonMean133.lean`.
These do not require the whole graph to be triangle-free, but they do
require singleton contacts and a triangle-free exterior. General #133
remains unresolved.

Use Lean 4.19.0 with Mathlib at `c44e0c8ee63ca166450922a373c7409c5d26b00b`
on `LEAN_PATH`, then run `bash graffiti-133-singleton-exterior/replay.sh`
from the repository root.
