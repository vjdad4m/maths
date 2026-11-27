# Graffiti.pc #189: the saturated order-16 case

Under the degree-four and 2-connected hypotheses of #189, if an edge-optimal
longest path with endpoints of degree at least four has eight edges and omits
seven vertices, Lean proves that the graph has a Hamiltonian path. Edge-optimal
means maximizing the edge count among the omitted vertices, subject to the
path being longest. The large-graph proof is structural; a small transparent
certificate supplies the path inside the remaining five-vertex graph.
The formal conclusion is `traceable_if_seven_off_saturated_four`, not a
solution to every order-16 case or to #189 generally.

Use Lean 4.19.0 with Mathlib at `c44e0c8ee63ca166450922a373c7409c5d26b00b`
and an existing Mathlib `LEAN_PATH`, then run
`bash graffiti-189-order-sixteen-saturated/replay.sh` from the repository root.
