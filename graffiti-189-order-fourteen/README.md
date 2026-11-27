# Graffiti.pc #189: the degree-four case through fourteen vertices

**Partial result for the full conjecture.** A 2-connected graph on at most fourteen vertices has a Hamiltonian path if at most one vertex has degree below four and every vertex has at most five vertices at even distance, counting itself.

The earlier [order-fourteen reduction](../graffiti-189-order-fourteen-shape/README.md) leaves one vertex outside an edge-optimal longest path. The formal model has two attachments to that path. The proof first uses the fact that adding the optional edges cannot decrease either endpoint's distance-two count, and then checks all twenty oriented attachment pairs in finite tables.

The tables provide either a spanning path in the model or a precise exceptional pattern. The exceptional certificate proves that any additional edge which could raise a specified path vertex's degree would violate a distance-two bound. The final Lean theorem transfers these results to the original graph.

- [Exact statement and graph transfer](src/FullFourteen189.lean), theorem `traceable_of_order_le_fourteen`.
- [Finite one-omission certificate](src/TinyFourOrder14One.lean) and [exceptional cases](src/ExceptionalFourOrder14One.lean).

In Lean and Mathlib 4.19.0, run `lake env bash /path/to/maths/graffiti-189-order-fourteen/replay.sh`. The tables use kernel computation and are separated into modules to make replay more practical. Larger graphs and the full conjecture remain open.
