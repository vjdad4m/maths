# Two-vertex cuts in the degree-four case of Graffiti.pc #189

The [Lean theorem](src/TwoCutFinal189.lean) shows that deleting two distinct vertices leaves at most two components in a finite 2-connected graph satisfying the degree-four and even-distance hypotheses of #189. Specifically, at most one vertex has degree below four, and each vertex counts at most five vertices at even distance, including itself. Consequently, every two-vertex cut in this setting leaves exactly two components. This is a reduction, not a Hamiltonian-path proof in the remaining cases.

For three components, consider the vertices in each component adjacent to either of the two deleted vertices. Vertices adjacent to the same deleted vertex but in different components compete for its neighbors' distance-two budgets. The Lean proof checks separately the case of three nonsingleton components and the case with a singleton. In the singleton case, the four distance-two slots at the singleton are all used by attachment vertices. The other vertices must then use slots at one of the two deleted vertices, which forces a tight size-five structure in each component and exceeds the budget.

## Replay

From a Lean 4.19.0 project with the Mathlib 4.19.0 build cache:

    lake env bash /path/to/maths/graffiti-189-two-cut/replay.sh
