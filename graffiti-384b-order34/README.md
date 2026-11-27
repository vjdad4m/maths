# Graffiti.pc #384b: the order-34 frontier

**Partial result.** Lean proves that any counterexample has a connected induced counterexample on at most 34 vertices with the same set of triangle counts. A least counterexample of order 34 has 33 distinct triangle counts. Its two triangular degree-two vertices, if both exist, cannot have disjoint attachment pairs with no cross edge between the pairs.

- [Induced counterexample reduction](src/Diversity35_384b.lean)
- [Order-34 structure](src/Frontier34_384b.lean)
- [Two-edge case](src/TwoEdgeExact34_384b.lean) and [remaining attachment patterns](src/TwoEdgeFinish34_384b.lean)

Smaller orders, the single-ear case, and other attachment patterns are not resolved here. The dependency archive contains Lean source only. The replay checks every source hash and compiles from source, not from stored proof objects.

In a Lean and Mathlib 4.19.0 project, run `lake env bash /path/to/maths/graffiti-384b-order34/replay.sh`.
