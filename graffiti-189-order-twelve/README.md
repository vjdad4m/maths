# Graffiti.pc #189: the degree-four case through twelve vertices

**Partial result.** A 2-connected graph on at most twelve vertices has a Hamiltonian path if at most one vertex has degree below four and every vertex has at most five vertices at even distance, counting itself.

The structural reduction produces a longest path of eleven vertices with one omitted vertex. After orienting and indexing the path, the omitted vertex attaches exactly at positions 1 and 9. The exact endpoint neighborhoods reduce to six membership bits and three optional edges, which Lean checks exhaustively. The surviving pattern has a spanning path. The transfer proof uses exact neighborhoods at the four checked vertices so that adding unmodelled edges elsewhere cannot invalidate the relevant lower bounds on distance-two counts.

- [Structural reduction and full order-twelve theorem](src/SmallOrderFour189.lean), theorem `traceable_of_order_le_twelve`.
- [Finite certificate and lift](src/TinyFourOrder12189.lean), checked by Lean's kernel without a native-evaluation axiom.

Replay in Lean and Mathlib 4.19.0 with `lake env bash /path/to/maths/graffiti-189-order-twelve/replay.sh`. The general conjecture remains open.
