# Graffiti.pc #189: degree-four case through order 17

**Theorem.** Let a finite simple graph with at most 17 vertices be 2-connected and have second-smallest degree at least four. If from every vertex at most five vertices are at even distance, counting the vertex itself, then it has a Hamiltonian path.

[Exact Lean theorem: `traceable_of_order_le_seventeen`](src/OffFour17Close189.lean).

The checked order-17 reductions rule out longest-path shapes with three, six, or five omissions and leave only a 12-edge path with four omitted vertices. The last case has an analytic proof when the omitted component is connected: the small marked core supplies a spanning path whose insertion improves the longest path. When the omitted vertices split into a three-vertex component and an isolated vertex, six normalized pairs suffice. The endpoint even-distance budget leaves exactly four forced zero marks, so the verifier only enumerates the remaining nonzero marks. Each surviving finite configuration has an explicitly checked longer path.

[Analytic partition](src/OffFour17Partition189.lean) · [Finite checker and all six rows](src/OffFour17DiscTable189.lean) · [Verification transcript](StrictReplay.log).

This settles the stated order and degree range, not all of Graffiti.pc #189. Replay with Lean and Mathlib v4.19.0 via `lake env bash /path/to/maths/graffiti-189-order-seventeen/replay.sh` from a prepared Mathlib checkout.
