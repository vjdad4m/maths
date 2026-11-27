# Graffiti.pc #189: a saturated 15-vertex case

This is a partial result, not a resolution of the conjecture. It concerns the
degree-four case: the graph is 2-connected, at most one vertex has degree less
than four, and each vertex has at most five vertices at even graph distance,
including itself. If an edge-optimal longest path with endpoints of degree at
least four has eight edges and omits six vertices, the graph has a Hamiltonian
path.

Here edge-optimal means that, among longest paths, the path maximizes the
number of edges induced by the vertices it omits. The proof uses rotations of that path
to restrict the possible attachments of the omitted vertices. It derives two
attachment vertices, each adjacent to every one of the four remaining omitted
vertices. The degree constraints force a spanning path among those four,
allowing all six omitted vertices to be spliced into a Hamiltonian path.

The target Lean theorem is `traceable_if_six_off_saturated_four`. The proof
does not assume an exhaustive computation. The certification script appends
the checked extensions to the prior source so the shared private lemmas remain
in scope. Use Lean 4.19.0 with Mathlib at
`c44e0c8ee63ca166450922a373c7409c5d26b00b` and an existing Mathlib
`LEAN_PATH`, then run `bash graffiti-189-saturated/replay.sh` from the repo
root. The theorem's axioms are printed by the check.
