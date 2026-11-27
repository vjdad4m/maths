# Graffiti.pc #189: order 17, five omissions excluded

In the degree-four, 2-connected scope of #189, Lean rules out an edge-optimal length-eleven path with high-degree endpoints and exactly five omitted vertices. An order-at-most-17 counterexample in this scope now has exactly 17 vertices and an edge-optimal path with **12 edges and four omitted vertices**. [Combined theorem](src/Order17OneBranch189.lean).

A [structural reduction](src/OffFive17CentralStructure189.lean) confines every remaining omitted component to two central attachment sites. The [graph transfers](src/OffFive17CentralTransfers189.lean) reduce the connected five-vertex case to a small marked-core route problem and the four-vertex component plus isolated vertex case to endpoint even-distance constraints. The finite tables have ten and five checked rows, respectively. [Scope closure](src/OffFive17Close189.lean).

The four-omission shape remains open here, as does the general conjecture. The [strict replay log](StrictReplay.log) uses only standard axioms. Replay from a prepared Mathlib v4.19.0 checkout: `lake env bash /path/to/maths/graffiti-189-order17-five-off/replay.sh`.
