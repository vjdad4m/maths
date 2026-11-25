# Graffiti.pc #261: total domination and degree-two vertices

Let G be a finite connected simple graph on n ≥ 2 vertices, S its set of degree-two vertices, x = |N(S) ∖ S|, t its total domination number, and L the maximum number of leaves of its spanning trees. [Conjecture #261](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/wowiiaii.pdf) asserts **2x ≤ tL**. (The one-vertex graph does not admit a total dominating set.) The catalogue lists it as open in its November 2026 snapshot. I found no prior proof of this exact statement; this is not a priority claim. This AI-assisted proof is posted for public review.

## Proof

1. **The non-degree-two vertices constrain the leaf number.** By [Karpov's Theorem 1](https://arxiv.org/abs/1205.5163), a graph with a vertices of degree 1 or 3 and b of degree at least 4 has a spanning tree with at least a/4 + b/3 + 3/2 leaves. No vertex has degree zero, so x ≤ a+b. Consequently x+6 ≤ 4L.
2. **Total domination constrains the order.** A minimum total dominating set D of size t induces at most floor(t/2) components, each of order at least two. Assign each vertex outside D to a component it touches and each vertex in D to its own component. The graph on these classes given by crossing edges is connected. Each edge of a spanning tree on the classes can be realized by a path between the two components using at most two vertices outside D. Adding these vertices to D gives a connected dominating set C of size at most 2t−2 (the classical Favaron–Kratsch bound). Take a spanning tree on C, and attach each outside vertex by one edge to C to make it a leaf. Thus n+2 ≤ L+2t. If t ≤ 3, D itself is connected, so the same construction gives n ≤ L+t.
3. **The cases.** Always t,L ≥ 2. If x≤2 the claim is immediate. Otherwise |S|≥2, because one degree-two vertex can cover only two neighbors, so x≤n−2. Also x+6≤4L forces L≥3.
   - If L≥4, then 2x≤2n−4≤2L+4t−8≤tL, the last gap being (t−2)(L−4).
   - If L=3 and t≥4, then x≤6 by step 1, so 2x≤12≤tL.
   - If L=3 and t≤3, then 2x≤2n−4≤2t+2≤3t by step 2.

This proves the bound for all orders. It is sharp: the path on three vertices has t=L=x=2.

## Verification

Lean 4.19.0 checks the arithmetic from the graph-theoretic premises, not Karpov's theorem or the rest of the graph-to-premises argument. The graph6 scanner independently verifies #261 and the neighboring #260 (as a separate empirical check, not a proof) on every connected unlabeled graph of orders 2–9. Its last two columns count equality cases for #260 and #261. It computes L as n minus the smallest size of a connected dominating set for n≥3: the non-leaves of any spanning tree are themselves a connected dominating set, and the reverse bound is shown in step 2. It treats n=2 separately.

```sh
lean Arithmetic261.lean
g++ -O3 -std=c++17 scan260261.cpp -o scan260261
(for n in {2..9}; do geng -cq "$n"; done) | ./scan260261
```
