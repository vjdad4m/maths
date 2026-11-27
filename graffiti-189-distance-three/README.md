# Graffiti.pc #189: all distance-three two-component cuts

**Partial result.** Lean proves that, under the degree-four even-distance hypotheses of #189, a two-connected graph has a Hamiltonian path if deleting two vertices at distance three leaves two components. The result no longer assumes either side has order four. It builds on the [order-four-side result](../graffiti-189-four-vertex-side) and excludes the case where both sides have five or more vertices.

See [ActualDistThree189.lean](src/ActualDistThree189.lean), theorem `traceable_at_actual_dist_three_cut`. The [two-cut reduction](../graffiti-189-two-cut) already shows that a two-vertex cut in this regime has exactly two components. Distance-one and distance-two cuts are not treated by this package; the general conjecture remains open.

In a Lean and Mathlib 4.19.0 project, run `lake env bash /path/to/maths/graffiti-189-distance-three/replay.sh`.
