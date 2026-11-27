# Graffiti.pc #189: the 2-connected degree-four case through order 15

Lean proves that every finite simple 2-connected graph on at most
**15 vertices** has a Hamiltonian path if at most one vertex has degree
below four and each vertex has at most five even-distance vertices,
counting itself. These are the degree-four hypotheses for #189.
This settles the stated size-and-connectivity slice, not the conjecture
at larger orders or for all other degree parameters.

The proof uses an edge-optimal longest path, whose endpoints can be
taken to have degree at least four. Structural arguments close the
branches with several omissions; the four-omission branch uses a
reduced finite model with 21 independently kernel-checked rows. If the
path omits just one vertex, that vertex has two neighbors and four
distinct distance-two contacts. This configuration forces order at most
13, so no new enumeration of the one-omission case is needed.

The main theorem is `traceable_of_order_le_fifteen` in
`src/TraceableOrderFifteenAssemblyVerified.leanpart`; the replay composes
the earlier certified sources so that their private helpers stay in scope.

Use Lean 4.19.0 and Mathlib at `c44e0c8ee63ca166450922a373c7409c5d26b00b`
on `LEAN_PATH`, then run `bash graffiti-189-order-fifteen/replay.sh`
from the repository root.
