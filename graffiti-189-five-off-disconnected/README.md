# Graffiti.pc #189: the full disconnected five-omission branch at order 16

In the degree-four, 2-connected setting, suppose the edge-optimal
longest path has ten edges and omits five vertices. If the subgraph
induced by the omitted vertices is disconnected, then the graph
has a Hamiltonian path.

The earlier mixed result covers a double contact within the
nontrivial omitted component. The complementary branch forces
that component to be a four-clique with individually attached
vertices. An exact sorted relabeling and two finite certificate
stages transfer the verified paths back to the original graph.
The 24 finite modules are reproduced from their exact Lean source
and checked in separate processes.

Main theorem:
`Graffiti189LongestPath.TwoCut.SmallOrderFour.traceable_if_five_off_disconnected`.
The connected omitted-subgraph branch remains open; this does not
settle order 16 or the general conjecture.

Use Lean 4.19.0 and Mathlib at
`c44e0c8ee63ca166450922a373c7409c5d26b00b` on `LEAN_PATH`.
Run `bash graffiti-189-five-off-disconnected/replay.sh` from the repository root.
