# Kelmans: geometry of the remote two-vertex deletion variant

This is a partial result. The Kelmans path-factor conjecture and the remote-edge version of the deletion problem are not settled here.

In a cyclically four-edge-connected cubic graph, choose adjacent vertices `x,y` to delete and a disjoint edge `uv` to omit. The remote condition asks for an orientation of the pair such that one of `x,y` is adjacent to neither end of `uv`. The [orientation theorem](src/RemoteT2Scope.lean) shows this is possible exactly when `xy` and `uv` are not opposite edges of a four-cycle (on the stated order domain).

The [cut-balance proof](src/RemoteT2PairStructure.lean) gives a lower bound of two on proper cuts of the graph left by deleting the adjacent pair; any width-two cut with two nonsingleton sides splits each pair of exposed ports. Omitting one more edge cannot disconnect the remaining graph, and if the edge is remote, it leaves at most one leaf.

One proof strategy is to reconnect the four exposed terminals by a pairing and apply an existing cyclically four-edge-connected factor theorem. The [14-vertex fixture](src/RemoteT2CompletionObstruction14.lean) rules out an unconditional such completion lemma even on the order-two-modulo-six domain: all three pairings introduce genuinely new edges, but each creates a triangle and therefore fails the needed cyclic connectivity. This is not a counterexample to the path-factor claim. A [positive cut inequality](src/RemoteT2SideCompletionCuts.lean) handles same-side pairing under a stronger cyclic-five boundary premise. The [three-edge transfer](src/RemoteT2AvoidThree.lean) is conditional on the supplied handle host, not a proof of three-edge avoidance.

Replay with Lean 4.19.0 and a prepared Mathlib 4.19.0 checkout: `lake env bash /path/to/maths/kelmans-remote-t2-geometry/replay.sh`. The source hashes and original [modular axiom check](StrictReplay.log) are included.
