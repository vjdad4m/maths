# Graffiti.pc #133: at most two exterior triangles at a dominating 7-cycle

Lean proves that the mean local independence number is at most four
under the following conditions: the finite simple graph has no ordinary
4-cycle and no induced nine-vertex path; it contains an induced 7-cycle;
each exterior vertex has exactly one neighbor on that cycle; and at most
two triangles are wholly outside the cycle. This includes two disjoint
triangles and two triangles that meet at one vertex.

First, any induced exterior subset with at most two triangles has
at most three more edges than vertices. Otherwise, choose a minimal
violating subset. Deleting a triangle vertex leaves at most one triangle,
so the prior edge bound forces high degrees at all triangle vertices.
Even when the triangles meet, at least five such vertices contribute too
much degree surplus. The six triangle incidences then account for the
possible three extra edges in the local-independence sum. A shared vertex
saves two because its two triangle-neighbor edges are disjoint.

The exact theorem is
`Graffiti133TwoExteriorTriangles.singleton_seven_at_most_two_exterior_triangles_mean_four`.
The intermediate theorem is `two_exterior_triangle_edge_bound`.
Three or more exterior triangles and general #133 remain unresolved here.

Use Lean 4.19.0 and Mathlib at `c44e0c8ee63ca166450922a373c7409c5d26b00b`
on `LEAN_PATH`, then run
`bash graffiti-133-two-exterior-triangles/replay.sh`.
