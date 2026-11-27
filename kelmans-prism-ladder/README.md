# Kelmans: arbitrary six-rung prism subdivisions

For an n-column cubic prism with n at least six and divisible by three, subdivide any six distinct rungs, with no restriction on their positions. Lean constructs a factor into three-vertex paths in the expanded graph. The proof follows a zigzag spanning path, traverses every marked rung so that the new vertices appear on the path, and partitions the path into successive triples.

The construction is an actual instance of the auxiliary Remote T2 problem, not just an abstract subdivision. The Lean wrapper checks cubicity, cyclic four-edge connectivity and three-vertex connectivity of the host, order two modulo six, the exact remote deletion and omission, and width at least three on nontrivial cuts of the survivor. The unrestricted conjecture remains open.

[General ladder and spanning-route construction](src/RemoteRungLadder.lean) · [Exact prism family](src/RemoteLadderPrismDomain.lean) · [Opened-cycle chain criterion](src/RemoteCycleChainCover.lean)

Compile with Lean and Mathlib 4.19.0 in `modules.txt` order. The [spaced-prism package](../kelmans-spaced-prism/) and its prerequisites supply the public module objects; see its dependency directions. Source SHA-256 values are recorded. Exact Lean replays used warnings as errors and standard axioms only.
