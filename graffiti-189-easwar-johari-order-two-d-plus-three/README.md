# Graffiti.pc #189: Easwar–Johari's order-2d+3 theorem in Lean

For a finite connected simple graph, let d be a nonnegative integer such that
at most one vertex has degree below d and every vertex has at most d+1 vertices
at even distance (counting itself). If deletion of any single vertex preserves
connectivity and the graph has order at most 2d+3, it has a spanning path.
Together with the earlier articulation result, this also covers all connected
graphs of order at most 13 under the degree-five hypotheses.

This is a Lean formalization of Theorem B(3) and Lemma 3.3 of
[Rohun Easwar and Shaurya Johari](https://arxiv.org/abs/2609.11719v1), not a
novel resolution of the conjecture. It uses the proved order-2d+2 case as a
predecessor. The indexed path-cut proof reassembles the path after adding and
then deleting a safe edge, treating both degree-sum slack cases.

Main declaration:
[`Graffiti189LongestPath.SmallOrder.traceable_at_order_le_two_d_add_three`](EJSlackClosure189.lean).
Use Lean and Mathlib 4.19.0 with the exact
[order-2d+2 package](../graffiti-189-easwar-johari-order-two-d-plus-two/)
and its documented dependencies on LEAN_PATH. Run `bash replay.sh`.
The [serial stage log](VERIFIED.log) records all newly checked modules,
with warnings as errors and only standard axioms.

[Complete pinned Lean sources](proof-sources.zip). Extract the archive and use its replay script.
