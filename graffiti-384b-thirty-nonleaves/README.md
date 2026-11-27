# Graffiti.pc #384b at 31 triangle-count types

A nonleaf here has degree at least two. Let T be the set of numbers of incident triangles realized at vertices, including zero when it occurs. A 2-dominating set contains at least two neighbors of each excluded vertex. At |T| = 31, the catalogue asks for a 2-dominating set of size at most n − 16.

## The isolated-vertex adapter

Every finite simple graph with 32 nonleaves and 31 triangle-count types satisfies the catalogue inequality when its order is 32 or 33. Connectedness is unnecessary for either statement. In particular γ₂ ≤ 16 at order 32 and γ₂ ≤ 17 at order 33. [IsolatedVertex31.lean](IsolatedVertex31.lean)

At order 33 the proof combines the previously verified adjacent-ear theorem, the no-leaf-attachment theorem and the leaf-attachment theorem. For order 32, adding a single isolated vertex necessarily increases γ₂ by one. It preserves the number of nonleaves and changes the triangle palette to T ∪ {0}. A hypothetical failure at this quota already realizes zero, by `Cover31.residual` and `Repair.maximal_diversity`. The enlarged graph has the same palette, its catalogue bound increases by one, and the order-33 theorem applies even though the new vertex is isolated.

## Necessary structure at 30 nonleaves

Let G be connected with exactly 30 nonleaves and 31 triangle-count types. If it fails the catalogue inequality, there is a connected induced failure on exactly 31 vertices with exactly the same palette and exactly 30 nonleaves. In particular, it suffices to study a graph with one leaf and 31 distinct counts. The general pruning theorem preserves the palette and gives order at most 31. Each nonleaf of the induced graph was already a nonleaf of G, and 31 types require at least 30 nonleaves. [Exact reduction and original-graph statements](ThirtyFinish31.lean)

Write H for the subgraph induced by all nonleaves of G, and R for the vertices of H adjacent in G to a vertex outside H. The earlier positive-core theorem gives H order 30, positive distinct scores and γ₂(H) = 15. The new conclusions under failure are as follows.

- H contains a five-clique and has a triangular vertex of degree two. Every vertex of R has degree at least four in H.
- There are two nonadjacent, uncredited cubic vertices u and s with triangle counts two and three respectively. They have at most one common neighbor. Both remain cubic with the same scores in G, and all their neighbors belong to H.
- The three neighbors of s meet every five-clique of H. At least three vertices of each five-clique belong to N(u) ∪ N(s). In particular, deleting the three neighbors of s leaves a graph with no five-clique.

The transversal assertion had previously been a hypothesis in an exploratory calculation at this order. The exact theorem now supplies it. The 30-nonleaf case with zero or one common neighbor of u and s remains open here. [Positive core and credits](ThirtyTransversal31.lean) · [Combined profile](ThirtyFinish31.lean)

## Proof and source map

| Module | Contribution and predecessor |
| --- | --- |
| IsolatedVertex31 | Defines the extension on a disjoint singleton and proves the exact palette, nonleaf and γ₂ identities. Combines LeafFinish, NoLeafAttachment and CompleteAdjacent. |
| ThirtyTransversal31 | Transfers the five-clique and triangular ear to the positive core. Reuses ForcedCubics.safe_cap, which allows two clique vertices to avoid all uncredited cubics. A cubic of score two can hit at most two members of a clique. Injectivity therefore forces the same score-three cubic to hit every five-clique. RootCut.cubic_root excludes a credited cubic. Its direct imports are CoverDense31 and CreditFinish31, independent of the isolated-vertex adapter. |
| ThirtyBoth31 | Extends the two-cubic requirement to arbitrary finite order under the stated half-order, credit, ear, clique and score hypotheses. The argument of BothCubics33 previously invoked an order-32 sampling theorem. Absence of the pair already forces the ear to be the only common neighbor of its endpoints. Restricting to edges in triangles preserves this property. HighEar.endpoint_profile then bounds the two endpoint degrees in that subgraph at any order. ForcedCubics.supported_degree excludes score two at both endpoints and the original contact-frame contradiction applies. |
| ThirtyPairSample31 | Adapts SharedSample33 to nine retained vertices from a pool of 26. Across the pool the scores skip both two and three. Lean verifies a total deficiency budget of 12,224,697. Four deficiencies per sample would require 4 × C(26,9) = 12,498,200, a gap of 273,503. |
| ThirtyPairSaving31 | Adapts SharedSaving33 to the 30-vertex core. Two shared neighbors meeting all five-cliques can be retained while omitting both cubics. The sample and at most three repairs give at most 2 + 9 + 3 = 14 retained vertices. |
| ThirtyFinish31 | Applies the published shared_transversal and clique_remainder lemmas. A second shared neighbor contradicts γ₂(H) = 15. Transfers degrees, scores, separation and codegree back to the original graph. Gives the exact induced order-31 reduction. |

The arithmetic uses Lean kernel reduction. No graph enumeration is required for the stated results.

## Replay

With Lean 4.19.0 and pinned Mathlib v4.19.0, put the already compiled prerequisites on the search path. For the isolated vertex module, use [order 33](../graffiti-384b-order33-full/) and its [leaf dependencies](../graffiti-384b-leaf-full/). For the 30-nonleaf modules, use [rich degree 31](../graffiti-384b-rich-degree31/) and [credit and five-clique cut](../graffiti-384b-five-clique-free31/) and their prerequisites. Compile the new modules in the order in `modules.txt` with `lean -DwarningAsError=true`, adding each compiled object to the search path. The original strict audit is below.

[Strict Lean replay](StrictThirty.log) · [Exact source hashes](NEW-SOURCES.sha256). The full conjecture remains open.
