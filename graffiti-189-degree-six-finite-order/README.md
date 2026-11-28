# Graffiti.pc #189: finite order reduction at second-smallest degree six

A finite connected simple graph in which every vertex has at most seven
vertices at even distance (itself included), and which has a vertex of
degree at most six, has at most **49 vertices**. In particular this bounds
every case of #189 whose actual second-smallest degree is six, regardless
of vertex connectivity. It does not prove that these graphs have Hamiltonian
paths.

Center distances at the low-degree vertex. There are at most seven even
vertices and six neighbors. Any odd vertex not a neighbor has a predecessor
at positive even distance along a shortest path. For each such predecessor,
fix its own preceding vertex on a shortest path to the center. Every odd
child is at distance exactly two from this preceding vertex, so there are at
most six choices per positive even predecessor, hence at most 36 odd vertices
beyond the neighbors. This bounds order by 7 + 6 + 36.

Lean theorem: `Graffiti189LongestPath.order_le_forty_nine_at_degree_six`.
Lean and Mathlib 4.19.0. Build the earlier
[SmallSeparator189](../graffiti-189-order-twelve/) dependency, then put its
checked object on LEAN_PATH and replay with
`lean -j1 -s65536 -DElab.async=false -DwarningAsError=true SixFiniteOrder189.lean`.
Strict audit uses only the three standard axioms.
