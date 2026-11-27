# Graffiti.pc #189: the degree-four, 2-connected case through order sixteen

For a finite connected simple graph, assume deleting fewer than two
vertices leaves it connected, every pair of distinct vertices has
at least one endpoint of degree at least four, and each vertex has
at most five vertices at even distance, counting itself. If the
graph has at most 16 vertices, Lean proves it has a Hamiltonian path.

The earlier shape theorem reduces any counterexample of this order
to a 16-vertex graph whose edge-optimal longest path misses either
four or five vertices. The published four-omission and five-omission
theorems exclude both. The general #189 conjecture is not settled.

Main theorem:
`Graffiti189LongestPath.TwoCut.traceable_of_order_le_sixteen`.

Use Lean 4.19.0 and Mathlib at
`c44e0c8ee63ca166450922a373c7409c5d26b00b` on `LEAN_PATH`.
Run `bash graffiti-189-order-sixteen/replay.sh` from the repository root.
The replay shares compiled objects across the archived branches.
It renames only the outer namespace in the earlier assembled shape
proof to keep its internal declarations separate from the other
modules, then checks the exact final theorem.
