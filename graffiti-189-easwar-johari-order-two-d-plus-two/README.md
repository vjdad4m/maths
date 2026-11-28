# Graffiti.pc #189: the Easwar–Johari small-order theorem

For a connected finite simple graph, let d be a nonnegative integer such that at most one vertex has degree below d and each vertex has at most d+1 vertices at even distance, including itself. If the graph has at most 2d+2 vertices, then it has a spanning path. In particular, threshold five is covered through order 12.

This formalizes Theorem B(2) and the disjoint-neighborhood edge closure (Lemma 3.2) of [Rohun Easwar and Shaurya Johari](https://arxiv.org/abs/2609.11719v1), not a new mathematical proof of the conjecture. The next size, 2d+3, is not part of this package.

Final declaration: [`Graffiti189LongestPath.SmallOrder.traceable_at_order_le_two_d_add_two`](src/EJOrderTwoClose189.lean).

Replay with Lean and Mathlib 4.19.0. Set LEAN_PATH to the objects for `OreClosure189`, `OreSpliceIndex189`, `ArticulationClosure189`, `ArticulationThree189`, and `DegreeFiveRouteBasic189` and their transitive dependencies, as used by the [degree-four](../graffiti-189-complete-degree-four/) and [degree-five](../graffiti-189-degree-five-cuts/) packages. Run `bash replay.sh`. The [strict replay transcript](VERIFIED.log) records each module's successful check and standard axioms; it was checked serially in stages.
