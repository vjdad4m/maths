# Graffiti.pc #189: order 17, six omissions excluded

In the degree-four, 2-connected scope of #189, Lean rules out an edge-optimal length-ten path with high-degree endpoints and six omitted vertices. A nontraceable graph on at most 17 vertices must now have order exactly 17 and an edge-optimal path of one of two shapes: **11 edges with five omissions**, or **12 edges with four omissions**. [Combined theorem](src/Order17TwoBranches189.lean).

The proof is structural. The six omitted vertices form one component or a five-vertex component and an isolated vertex. The nontrivial omitted component only uses single interior attachments. Two elementary [marked-path lemmas](src/SixCoreMarkedPath189.lean) supply a path of at least three edges between selected attachments on a five- or six-vertex core. The only six-vertex exceptions are marked leaf-neighbor pairs, which the even-distance bound excludes here. The [splice](src/OffSix17CoreLift189.lean) contradicts the original path's optimality. The two small core lemmas use finset cardinality, not a graph enumeration or a finite search table.

This closes only the six-omission shape. It does not settle order 17 as a whole or the general conjecture. [Strict replay transcript](StrictReplay.log). Replay with Lean and Mathlib v4.19.0 via `lake env bash /path/to/maths/graffiti-189-order17-six-off/replay.sh` from a prepared Mathlib checkout.
