# Graffiti.pc #133: at most one exterior triangle at a dominating 7-cycle

Let a finite simple graph have no ordinary 4-cycle and no induced
nine-vertex path. Suppose it has an induced 7-cycle, every vertex
outside it has exactly one neighbor on it, and there is at most one
triangle wholly outside the cycle. Lean proves that the mean local
independence number of the whole graph is at most four.

A stronger intermediate result bounds the edge count of any induced
exterior subset with at most one triangle by its order plus one.
A minimum induced obstruction either has a degree-two deletion or can
be reduced by contracting its unique triangle. The remaining possibilities
lift to theta or figure-eight configurations. The finite certificates
check each applicable small attachment at the induced 7-cycle; the
symbolic lift transfers an induced nine-vertex path to the host graph.
The loss in local independence at vertices of a triangle pays for the
one additional exterior edge.

The exact theorem is
`Graffiti133OneTriangle.singleton_seven_at_most_one_exterior_triangle_mean_four`.
The edge bound is `Graffiti133ExpandedTriangle.one_exterior_triangle_edge_bound`.
This does not cover arbitrary exterior triangles or solve general #133.

Use Lean 4.19.0 and Mathlib at `c44e0c8ee63ca166450922a373c7409c5d26b00b`
on `LEAN_PATH`. From the repository root run
`bash graffiti-133-one-exterior-triangle/replay.sh`.
