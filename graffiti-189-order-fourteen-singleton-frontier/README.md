# Graffiti.pc #189: order-fourteen singleton-shore frontier

A connected finite graph stays connected after deletion of any vertex,
has at most one vertex of degree below five, and at most six vertices
at even distance from each vertex, counting itself. Suppose deleting
two adjacent vertices leaves two shores of sizes one and eleven. This
stage narrows any counterexample to seven parity profiles modulo
interchanging the two cut vertices, but does not resolve those seven
profiles.

The key declarations are `AdjProfile.compact_fourteen_singleton`
(arithmetic, thirteen profiles up to symmetry), `adjacent_singleton_terminal_count`
(each terminal has at least three neighbors in the large shore, all of
which are high), `unique_exclusive_ports_nonadjacent_of_three_both`
(saturated parity across the large shore), and
`frontier_of_adjacent_singleton_eleven_counterexample` (the seven profiles).
The last three live in namespace
`Graffiti189LongestPath.CrossSaturation.FiveAdjacent`.

The proof uses Lean 4.19.0 with Mathlib 4.19.0. With the previously checked
dependency objects on `LEAN_PATH`, the modules listed in `order.txt`
check in serial; `./replay.sh` performs this check. Direct external
dependencies are the established compact-profile and order-sixteen
singleton packages, and the verified nonadjacent-cut dispatcher.
`LEAN-CHECK.txt` gives the exact standard-axiom reports.
