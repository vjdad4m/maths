# Graffiti.pc #189: the degree-four case through thirteen vertices

**Partial result.** A 2-connected graph on at most thirteen vertices has a Hamiltonian path if at most one vertex has degree below four and every vertex has at most five vertices at even distance, including itself.

Choose a longest path with endpoints of degree at least four, maximizing the edge count within its support among longest paths. Lean constructs spanning paths in the cases with three or four omitted vertices and excludes the two-omission case. With one omission at order thirteen, the argument normalizes its two attachments to path positions 1 and (j), where (4le jle10). Seven finite tables check the admissible mark patterns. The proof then lifts a spanning path in the surviving model to the original graph.

- [Exact theorem and transfer](src/SmallOrderFour189.lean), theorem `traceable_of_order_le_thirteen`.
- [Finite model](src/TinyFourOrder13Model189.lean) and [certificate](src/TinyFourOrder13189.lean). The seven tables use kernel reduction, not native evaluation.

From a Lean and Mathlib 4.19.0 project, run `lake env bash /path/to/maths/graffiti-189-order-thirteen/replay.sh`. Larger graphs and the full conjecture remain open.
