# Graffiti.pc #189: distance-three cuts with a four-vertex side

**Partial result.** Under the degree-four hypotheses of #189, if a two-vertex cut has its vertices at distance three and leaves a component of order four, Lean proves that the other component has at most six vertices and the graph has a Hamiltonian path. This does not assume the other component is small.

See [FourSideClose189.lean](src/FourSideClose189.lean), `other_order_le_six` and `traceable_of_four_side`. The general conjecture remains open.

In a Lean and Mathlib 4.19.0 project, run `lake env bash /path/to/maths/graffiti-189-four-vertex-side/replay.sh`.
