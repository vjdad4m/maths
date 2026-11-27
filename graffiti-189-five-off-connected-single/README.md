# Graffiti.pc #189: five omissions with connected, individually attached vertices

Under the degree-four and two-connectivity assumptions at order 16,
take an edge-optimal longest path of ten edges omitting five vertices.
This package handles the remaining case in which those vertices
induce a connected graph and each has at most one contact on the path.

Exact endpoint scores and sorted port labels produce 45 finite
rows. The corrected row gate enforces the original requirement that
at most one vertex has degree less than four, using internal degree
plus the exact port incidence. Ordinary kernel checks cover the
positive row paths and the graph proof excludes the two exceptional
masks using a five-vertex distance-two contradiction.

The final module proves
`traceable_if_five_off_connected_single` and, by including the
earlier disconnected and connected-double results,
`traceable_if_five_off_order_sixteen`. These are scoped to the
five-omission path shape, not the full unrestricted conjecture.

Use Lean 4.19.0 and Mathlib at
`c44e0c8ee63ca166450922a373c7409c5d26b00b` on `LEAN_PATH`.
Run `bash graffiti-189-five-off-connected-single/replay.sh` from
the repository root. The script checks all 68 exact generated Lean
sources before rebuilding in separate processes.
