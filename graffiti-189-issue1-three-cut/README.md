# Graffiti.pc #189: a 34-vertex three-component minimum cut

A **counterexample to a proposed shortcut, not to #189**. Even if one can choose the minimum separator, there need not be one leaving exactly two components. The concrete connected graph here satisfies the even-distance premise of #189 and has a Hamiltonian path.

**Attribution.** [duggiephresh's issue #1](https://github.com/vjdad4m/maths/issues/1) introduces the eight-vertex base `G?qtfo` and a clique blow-up with part sizes `(L−12,4,2,6,6,1,1,L−4)` for L ≥ 16. This certificate uses a *modified* weighting, moving one vertex from B to D, at L = 15. It does not attribute the modified weighting to the contributor or claim a Lean proof for every L.

## Construction and checks

The bags A, B, D, P, Q, x, y, Z have sizes **3,3,3,6,6,1,1,11**. Each is a clique; complete joins are AD, Ax, Ay, AZ, BD, BZ, DZ, Px, Py, PZ, Qx, Qy, QZ. The vertices are numbered consecutively starting from zero in that bag order.

* The graph has 34 vertices, a triangle and diameter 3. Every degree is at least 15 and both singleton vertices have degree 15; hence the second-smallest degree σ is exactly 15. The largest number of vertices at even distance (including the vertex itself) is 16 = σ+1. These counts use Mathlib's graph distance; the distance table is proved correct by constructing a walk of each advertised length and proving no shorter walk is possible.
* The 13 vertices in x, y and Z form the unique minimum vertex separator, so κ = 13 = σ−2, and n = 2σ+4. To handle **arbitrary vertex deletions**, project one surviving side to its set of bag indices. Every vertex in a neighbouring bag outside that support must have been removed. An exhaustive check on the *eight* indices shows the boundary contains AZ, DZ, APQ or xyZ; their vertex weights are respectively 14, 14, 15 and 13. At budget 13 only xyZ is possible, and the deletion must equal it.
* Removing xyZ leaves exactly three connected components, the vertices of A∪B∪D, P and Q. Lean constructs an equivalence from the induced graph's Mathlib connected components to `Fin 3`.
* Concatenating the cliques in order **P, x, Q, y, A, D, B, Z** visits every vertex exactly once. The listed path is a Mathlib walk with nodup support and each vertex has support count one.

The combined theorem is **`Issue189.regression`**, in [Summary189.lean](Summary189.lean). Diameter and triangle statements are in the same file. The concrete proof neither resolves #189 nor limits how many components might occur for other graphs.

## Replay

Use Lean 4.19.0 and Mathlib at `c44e0c8ee63ca166450922a373c7409c5d26b00b`. From a mathlib project on this revision, run `lake env bash /path/to/this/directory/replay.sh`. Alternatively set `LEAN_BIN` to the executable and `LEAN_PATH` to the compiled Mathlib and dependency search paths. The script creates a fresh temporary object directory and treats warnings as errors. There is no SAT solver or external certificate; the finite computations are checked by the Lean kernel.
