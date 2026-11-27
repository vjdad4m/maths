# Graffiti.pc #133: two-gate extensions of an induced core

In a finite simple graph with no four-cycle, suppose an induced core
already has average local independence at most four. Every vertex
outside the core must see at least one of two designated core
vertices, and have no other neighbors in the core. Then the whole
graph has average local independence at most four. No restrictions
on the number of exterior vertices, edges or triangles are needed.

The proof protects the core while taking a smallest induced subgraph
that would violate the bound. Removing any exterior vertex in that
subgraph supplies a lower bound on its degree after accounting for
triangles. The two-gate structure contradicts that local inequality.

The two dominating-seven-cycle theorems give immediate instances of
the core premise. This is a nested-core result with a specific
attachment condition, not a proof for arbitrary nested dominating
cores or of the entire conjecture.

Use Lean 4.19.0 and Mathlib at
`c44e0c8ee63ca166450922a373c7409c5d26b00b` on `LEAN_PATH`.
Run `bash graffiti-133-nested-c7-two-gate/replay.sh` from the repository root.
