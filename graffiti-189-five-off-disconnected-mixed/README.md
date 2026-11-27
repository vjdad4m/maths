# Graffiti.pc #189: disconnected five-omission case with a double contact

In the degree-four, 2-connected, order-16 setting, take an
edge-optimal longest path of ten edges omitting five vertices.
Assume the omitted subgraph is disconnected and some omitted
vertex with an omitted neighbor has two contacts on the path.
Then the graph has a Hamiltonian path.

The omitted subgraph has a four-vertex component and one isolated
low-degree vertex. The two double-contact vertices are forced to
use disjoint pairs of sites. A kernel-checked 13-label model gives
exactly two valid endpoint-mark patterns. Each lifts to an explicit
spanning path in the actual graph.

The exact theorem is
`Graffiti189LongestPath.TwoCut.SmallOrderFour.traceable_if_five_off_disconnected_mixed`.
It does not close the remaining disconnected single-contact or
connected cases, or the general conjecture.

Use Lean 4.19.0 and Mathlib at
`c44e0c8ee63ca166450922a373c7409c5d26b00b` on `LEAN_PATH`.
Run `bash graffiti-189-five-off-disconnected-mixed/replay.sh` from
the repository root.
