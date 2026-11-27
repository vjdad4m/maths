# Graffiti.pc #199: excluding the canonical four-block packing

For the exact canonical four-block packing, including its degree conditions,
Lean proves incompatibility with vertex connectivity at least three and
induced-tree number at most five. No independence-number restriction, size
restriction, or disjointness of the singleton high sets is needed in this
theorem.

If the paired blocks share at most two high vertices, delete those vertices.
A shortest remaining connector extends to an induced six-vertex path.
If the paired blocks share at least three high vertices, deleting at most
two private high vertices instead separates the paired region from a
singleton root, contrary to the connectivity assumption.

The theorem is `FourBlockPacking.impossible_of_connectivity_three_tree_budget`
in `src/CoveredPackingObstruction.lean`. It does not establish that a minimum
counterexample to #199 has the canonical packing and degree conditions,
nor handle arbitrary connectivity and induced-tree parameters. The full
conjecture remains open.

Use Lean 4.19.0 and Mathlib at `c44e0c8ee63ca166450922a373c7409c5d26b00b`
on `LEAN_PATH`, then run
`bash graffiti-199-canonical-four-block-obstruction/replay.sh`.
