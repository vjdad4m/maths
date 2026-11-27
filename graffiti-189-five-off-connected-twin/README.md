# Graffiti.pc #189: five connected omissions with a double contact

Under the degree-four and two-connectivity assumptions at order 16,
suppose the edge-optimal longest path has ten edges and omits five
vertices inducing a connected graph. If any omitted vertex has two
contacts on the path, then the full graph has a Hamiltonian path.

A double-contact vertex exhausts its distance-two allowance with the
four path flanks. Thus it is adjacent to every other omitted vertex,
and every contact of the omitted graph lands at one of its two
path sites. Sorted labeling and exact distance transfer reduce
the remaining configurations to independently checked finite rows.

Main theorem:
`Graffiti189LongestPath.TwoCut.SmallOrderFour.traceable_if_five_off_connected_twin`.
The connected all-single-contact case and the general conjecture
remain open.

Use Lean 4.19.0 and Mathlib at
`c44e0c8ee63ca166450922a373c7409c5d26b00b` on `LEAN_PATH`.
Run `bash graffiti-189-five-off-connected-twin/replay.sh` from the repository root.
