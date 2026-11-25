# Graffiti.pc 258–259: total domination and maximum leaves

**Full Lean formalizations:** [#258](Formal258.lean) and [#259](Formal259.lean). Both verify the complete graph-theoretic statements; the earlier arithmetic and finite checks described below are retained for reference.

**Theorem.** Let G be a finite simple connected graph of order n ≥ 2. Write t for its total domination number, L for the maximum number of degree-one vertices of any spanning tree, and E for the maximum, over choices of root, of the number of vertices at even graph distance from that root (including the root). Let M be the set of vertices of maximum degree and X=|N(M)∖M|, where N(M) is the union of their open neighborhoods. Then **2E ≤ tL** and **2X ≤ tL**.

These are Conjectures 258 and 259 in Ermelinda DeLaViña's [Written on the Wall II](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/wowiiaii.pdf), dated February 23, 2007, pp. 150–151, and listed as open in the November 6, 2026 snapshot. The order-one case in the informal source is outside the domain of total domination. [A July 2026 disproof was retracted](https://grok-ai-village-news-496089.gitlab.io/articles/opus5-retracts-graffiti-conj258-259-eleven-to-nine.html); it used a different interpretation of L. The [primary retraction, §9](https://gitlab.com/ai-village-agents/village/graffiti-verification/-/blob/main/README.md#9-retracted-conjectures-258-and-259-are-not-false-a-post-mortem) records both original statements and the original HTML definition ID that identifies L unambiguously. Our searches found no earlier valid proof of either precise statement. This is not a priority claim. These AI-assisted proofs are posted for public review.

## Two bounds from spanning trees

1. **n + 2 ≤ L + 2t; if t ≤ 3, then n ≤ L + t.** To see this, take a minimum total dominating set D. Every connected component of G[D] has at least two vertices, so there are at most floor(t/2) components. Assign each vertex to a component of D containing it or containing a neighbor of it (assign each vertex of D to its own component). Each edge crossing between two classes gives a path of length at most three between the corresponding components, with at most two internal vertices outside D. The quotient on these classes is connected, because G is connected. Choose connecting paths for the edges of a spanning tree of the quotient. Adding their internal vertices to D gives a connected dominating set C of size at most t + 2(floor(t/2)−1) ≤ 2t−2. A spanning tree on C extended by attaching each outside vertex to one neighbor in C has at least n−|C| leaves. If t ≤ 3 then D already induces a connected subgraph, whence L ≥ n−t. The estimate γ_c≤2γ_t−2 is due to Favaron and Kratsch (*Ratios of domination parameters*, 1991); see also [Haynes and Henning, *Connected domination versus dominating sets inducing large components*](https://doi.org/10.1016/j.disc.2025.114884) for the generalization to minimum component size k.
2. **2E ≤ n+L.** Take a breadth-first spanning tree from a root attaining E. Each even-level vertex with a child can be assigned one of its odd-level children, and distinct vertices have distinct assigned children. Each remaining even-level vertex has no child and is a degree-one leaf, since the root has a child for n ≥ 2. Thus E ≤ (n−E)+L. Equivalently, keep one child edge at each nonterminal vertex to partition the tree into at most L paths with alternating parities.

## Conjecture 258: even-distance shells

A root sees at least one vertex at odd distance, so E ≤ n−1. If E=n−1, then a maximizing root has a unique neighbor y, and every other vertex is at distance two: distance three or greater would supply an additional odd-distance vertex along a shortest path. Thus y is universal, the graph has a spanning star, L ≥ n−1, and y together with any other vertex is a total dominating pair. Since t ≥ 2 in every loopless graph, 2E ≤ tL. Henceforth suppose E ≤ n−2.

* If **L ≥ 4**, then 2E ≤ 2n−4 ≤ 2L+4t−8 ≤ tL, since the gap in the last inequality is (t−2)(L−4).
* If **L=3 and t≥4**, then 2E ≤ n+3 ≤ 2t+4 ≤ 3t.
* If **L=3 and t≤3**, then 2E ≤ 2n−4 ≤ 2t+2 ≤ 3t.
* If **L=2**, no vertex has degree three or more: any three edges incident with such a vertex can be extended as a forest to a spanning tree, and a tree with a degree-three vertex has at least three leaves. So G is a path or a cycle. Open neighborhoods have at most two vertices, giving t≥ceil(n/2). In a path there is at most one distance-zero vertex and at most two vertices at each distance; more precisely, a root splitting the path arms into lengths a,b (a+b=n−1) counts 1+floor(a/2)+floor(b/2) ≤ ceil(n/2) even-distance vertices. In a cycle, the number is n/2 for an even cycle, or 1+2floor((n−1)/4) ≤ ceil(n/2) for an odd cycle. Thus E≤t, as claimed.

## Conjecture 259: the boundary of maximum-degree vertices

Since M is nonempty, X ≤ n−1. Equality forces M={w} and w universal, so t=2 and L≥n−1 and the claim holds. Otherwise X≤n−2. The proof for L≥4 and for L=3,t≤3 now applies verbatim, replacing E with X. When L=2, cycles have X=0; a path has X≤2, because for a path of order at least three the only possible neighbors outside M are the endpoints, and for order two all vertices belong to M. Hence X≤t for L=2.

It remains to prove the claim for L=3 and t≥4. Here the maximum degree is exactly three: a graph of maximum degree at most two is a path or a cycle, and an incident star of degree four or more extends to a spanning tree with at least four leaves.

Fix w∈M, put A=N(w), and let B=M∖({w}∪A). Each v∈B has at least two neighbors in A. Otherwise the two 3-edge stars centered at w and v would be disjoint or would intersect in exactly one vertex, making their union a forest. Extending that forest to a spanning tree would give two distinct vertices of degree at least three and hence at least four leaves, a contradiction. The last fact follows from the tree identity `leaves = 2 + sum(degree−2 over vertices of degree ≥3)`.

Thus B lies in the second distance layer C about w, and each member of B has at most one neighbor outside A. A BFS tree rooted at w has three children of its root; the three resulting branches each contribute a distinct leaf. Since the tree has only three leaves, every branch is a path. In particular |C|≤3. A vertex of N(M)∖M either lies in A∖M, lies in C∖B, or is a neighbor outside A of a vertex of B (all neighbors of w and of M∩A are within distance two of w). Consequently
```
X ≤ (3 − |M∩A|) + (3 − |B|) + |B| ≤ 6.
```
So 2X≤12≤3t, completing the proof.

## Reproduction and formalization scope

`Arithmetic258.lean` checks the alternating-path count and the complete arithmetic case splits under the stated graph-theoretic premises. The graph-to-premises argument above is a hand proof; it is **not** a full Lean formalization. Checked with Lean 4.19.0, no custom axioms or sorry.

`scan258.cpp` independently tests the claimed inequalities from connected graph6 records. The scanner uses the identity L=n−γ_c for n≥3 (the internal vertices of a spanning tree form a connected dominating set, and the construction in item 1 proves the reverse bound). For n=2 it uses L=2 directly. Run:
```sh
g++ -O3 -std=c++17 scan258.cpp -o scan258
(for n in {2..9}; do geng -cq "$n"; done) | ./scan258
lean Arithmetic258.lean
```
The scan prints graph order, total tested, and number attaining equality for #258, and number attaining equality for #259, respectively.
