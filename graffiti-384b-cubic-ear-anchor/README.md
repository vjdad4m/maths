# An exact 29-vertex test for a cubic ear attachment in Graffiti.pc #384b

Let G have order 33 and 33 different vertex triangle-incidence counts. A 2-dominating set provides two neighbors to every vertex outside the set. The conjectured upper bound on its minimum size is 16. In the previously reduced leaf-and-ear case, deleting the leaf z gives a 32-vertex core H with positive pairwise distinct triangle counts, a five-clique, and 2-domination number 16. The results here address the case where the leaf attaches at a neighbor a of the triangular ear e in H. Denote its other neighbor by c, and let J be the 29-vertex graph induced by deleting e, a and c from H.

**If a has degree three in H, then γ₂(G) = γ₂(J) + 2.** The possible pairs (γ₂(J), γ₂(G)) are (14,16) and (15,17). The order-33 conjectured bound therefore holds exactly when J has a 14-vertex 2-dominating set. The theorem gives an exact test for each graph satisfying the hypotheses. Whether the second value is realizable with 33 distinct counts remains open. J may have different triangle counts from those in G. The theorem makes no connectivity or diversity assertion about J. [Full-graph identity, core equivalence and route restriction](FinishAnchor33.lean)

## How the test works

1. For an attachment at either ear neighbor, at any degree, a successful exchange is equivalent to finding a set X of at most 14 vertices which 2-dominates J and contains a neighbor of c in H. The successful full set is X together with e and z. In a core minimum set that can be exchanged, both e and a are selected. The ear would otherwise lose its second neighbor when a is exchanged for z. The opposite anchor c is omitted because a has exactly one selected neighbor. Deleting a and e gives X. The lifting direction uses the previous minimum-set exchange equivalence. [Exact neighborhood condition](AnchorDeletion33.lean)
2. Suppose a is cubic in H. Its third neighbor w sees c, and e and a have triangle counts 1 and 2. In a failure, the earlier five-clique theorem places c and w in every five-clique. Four clique vertices remain in J, all adjacent to c. If J has minimum degree at least three, pin those four vertices two per side and maximize the cut. Both sides 2-dominate J and meet the neighborhood of c. The smaller side has at most 14 vertices. [Pinned cut](AnchorCut33.lean) · [Cubic analysis](CubicAnchor33.lean)
3. Consequently any failure has a vertex v with residual degree at most two. The counts 1 and 2 are already occupied. Counting its lost neighbors forces v to be cubic in H with exactly three triangles and adjacent to c. Injectivity makes it the unique low vertex in J. Its two remaining neighbors p and q form a triangle with v and both see c. Every 2-dominating set of J now meets the neighborhood of c, either at v or through its neighbors. A maximum-cut argument including v in both candidate sets gives γ₂(J) ≤ 15. Restoring e and c gives γ₂(H) ≤ γ₂(J) + 2. These bounds and the exchange test prove the identity. In particular, an attachment with no cubic count-three neighbor of c in J satisfies the conjectured bound. [Core equivalence](FinishAnchor33.lean)
4. If the full value is 17, every simple p–q path in J avoiding v has odd length, and meets any clique of size at least three disjoint from v in at most one vertex. Indeed, the first and last visits to such a clique could be joined either directly or via a third clique vertex, producing an even path. There is a simple alternative path of odd length at least three. Its edges and the closing edge pq form an even cycle. In H the edge pq has exactly two common neighbors, c and v. Every other edge along that cycle has at most one common neighbor in H, and the only possible one is c. This is a necessary condition for failure expressed in the original core. [Path parity](ParityAnchor33.lean) · [Exact common-neighbor restrictions](AnchorEdge33.lean)

The earlier six-vertex example distinguishes two roots having the same degree and triangle count. Both roots in that example miss the ear. The new result uses adjacency to the ear and clique and path structure. Higher-degree roots on the ear retain the neighborhood condition in step 1. Attachments away from the ear and smaller diversity are still open here.

## Sources and replay

| New module | Direct import | Main declaration |
| --- | --- | --- |
| AnchorDeletion33 | EarOnClique33 (frozen baseline) | exchange_iff_guarded |
| AnchorCut33 | AnchorDeletion33 | guarded_cut |
| CubicAnchor33 | AnchorCut33 | cubic_failure |
| ParityAnchor33 | CubicAnchor33 | even_of_two_contacts, odd_routes |
| FinishAnchor33 | ParityAnchor33 | core_exchange, full_value, failure_routes |
| AnchorEdge33 | FinishAnchor33 | thin_cycle |

The proof reuses the #384b declarations EarRoot33.attachment_iff, EarOnClique33.cubic_root_cliques, PinnedColor34.cut, OneEar.route_of_reach and CoreColor33.closeRoute and split. The public #397c lift starts from a dominating set of the graph square and charges nonsupports. The #299 transversal bound estimates the size of a set meeting fixed clauses. Neither supplies the reverse implication for ordinary 2-domination of the induced residual. [Shared checked index](https://github.com/vjdad4m/maths/blob/main/README.md) · [Proof397c](https://github.com/vjdad4m/maths/blob/main/graffiti-397c/Proof397c.lean) · [Proof299](https://github.com/vjdad4m/maths/blob/main/graffiti-299/Proof299.lean)

Use Lean 4.19.0 and the prepared Mathlib 4.19.0 checkout at
`c44e0c8ee63ca166450922a373c7409c5d26b00b`. The replay rebuilds the
published [leaf-exchange foundation](../graffiti-384b-ear-exchange/)
and the six new modules with warnings as errors. From the repository root:

```bash
CROSSFOUR_LEAN_BIN=/absolute/path/to/lean-4.19.0-linux/bin \
CROSSFOUR_MATHLIB=/absolute/path/to/mathlib4-4.19.0 \
bash graffiti-384b-cubic-ear-anchor/replay.sh
```
