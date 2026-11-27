# Graffiti.pc #189: order 17, three omissions excluded

The precise scope is the second-smallest degree at least four in a 2-connected finite simple graph, under the catalogue's bound that each vertex sees at most five vertices at even distance, including itself.

[Lean rules out a high-ended edge-optimal path of length 13 with three omitted vertices](src/OffThree17Close189.lean). It uses direct boundary splices, reflection, and 16 finite interior cases, all checked by Lean with standard axioms. The wrappers use the earlier order-16 proof, so a nontraceable graph on at most 17 vertices in this scope has exactly 17 vertices and an edge-optimal path in one of three remaining shapes: 10 edges with six omissions, 11 edges with five omissions, or 12 edges with four omissions. See [the combined theorem](src/Order17ThreeBranches189.lean).

This does not settle order 17 in full, or the conjecture at other degrees and orders. The [strict replay transcript](StrictReplay.log) records the modular checks. Rebuild with Lean 4.19.0 and Mathlib 4.19.0 by running `lake env bash /path/to/maths/graffiti-189-order17-three-off/replay.sh` from a prepared Mathlib checkout.
