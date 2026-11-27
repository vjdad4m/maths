# Graffiti.pc #189: reduction to one omitted vertex at order fourteen

**Partial result.** Consider a graph on at most fourteen vertices with the degree-four and 2-connectivity hypotheses: at most one vertex has degree below four, and every vertex has at most five vertices at even distance, including itself. If it has no Hamiltonian path, Lean proves that it has exactly fourteen vertices and that an edge-optimal longest path with high-degree endpoints contains thirteen of them. In particular, the cases with two, three, four, or five omitted vertices do not produce a counterexample in this reduction.

The proof uses a labelled finite certificate for the three-omission case, an exact contradiction for the four-omission case, and a spanning-path construction for the five-omission case. The remaining one-omission finite classification is **not** included.

See [the exact one-omission reduction](src/ShapeFourteen189.lean), theorem `order_fourteen_shape`, and [the three-omission kernel certificate](src/TinyFourOrder14Three.lean). This package builds from the [order-thirteen proof](../graffiti-189-order-thirteen/README.md). Replay in a Lean and Mathlib 4.19.0 project with `lake env bash /path/to/maths/graffiti-189-order-fourteen-shape/replay.sh`.
