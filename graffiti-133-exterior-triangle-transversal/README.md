# Graffiti.pc #133: removing low-degree vertices that hit exterior triangles

Assume a finite graph with no ordinary 4-cycle and no induced 9-vertex
path has an induced 7-cycle with exactly one cycle neighbor per outside
vertex. Let `D` be a set of outside vertices that meets every exterior
triangle, with degree at most two in the exterior at each vertex of
`D`. If at least `2 * |D|` distinct host vertices belong to triangles,
then Lean proves that the mean local independence number is at most four.

The earlier [triangle-free exterior theorem](../graffiti-133-singleton-exterior/)
controls the number of edges after removing `D`. Each removed vertex
costs at most one in the edge excess. A vertex lying on a triangle
contributes at least one less to local independence than to degree,
which supplies the necessary correction.

This includes the case of one exterior triangle with an exterior-degree-two
vertex. The theorem is `triangle_transversal_mean_four` in
`src/BicycleTriangleDeletion133.lean`; the special case is
`one_exterior_triangle_low_degree_mean_four`. Arbitrary exterior triangles
and general #133 are not resolved by this package.

Use Lean 4.19.0 and Mathlib at `c44e0c8ee63ca166450922a373c7409c5d26b00b`
on `LEAN_PATH`, then run
`bash graffiti-133-exterior-triangle-transversal/replay.sh`.
