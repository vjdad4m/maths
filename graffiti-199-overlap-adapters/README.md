# Graffiti.pc #199: same-half splices and graph adapters

**Partial results.** The previous package handled a three-singleton configuration when the shared triangle tips lie in opposite halves. Lean now checks the same-half splice and the labelled adapter for either placement. The endpoint is a Hamiltonian path in Mathlib, under the precise block, degree, independence, and induced-cut assumptions in the theorem.

- [Three-singleton Hamiltonian path, both tip placements](src/PairedOverlapAdapter.lean)
- [Same-half splice and graph interpretation](src/SameHalfSplice.lean) and [its neighborhood adapter](src/NeighborhoodAdapter.lean)
- [Order-15 and order-16 depleted-block adapters](src/DepletedBlockAdapter.lean) and [terminal loss interface](src/TerminalLossAdapter.lean)

The missing reduction is to derive these labelled hypotheses from an arbitrary minimum counterexample to #199. This package does not prove that reduction or settle the conjecture.

In Lean and Mathlib 4.19.0, run `lake env bash /path/to/maths/graffiti-199-overlap-adapters/replay.sh` to rebuild all 17 local source modules.
