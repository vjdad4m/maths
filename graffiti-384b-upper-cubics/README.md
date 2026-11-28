# Graffiti.pc #384b in the upper triangle-edge profile

Let G be a finite simple graph, let T be its set of distinct vertex triangle-incidence counts, and write J for the spanning graph retaining all edges that belong to a triangle. Let H be the vertices of degree at least three in J. The conclusions apply to a putative failure of γ₂(G) ≤ |V(G)| − ⌈|T|/2⌉ satisfying |H|+1=|T|.

If H is nonempty, J has exactly two cubic vertices. Their triangle counts in G are 2 and 3, they are nonadjacent in J, and they are exactly the high vertices with two crossing neighbors in **every** maximum cut of J. Both vertices are independent of the choice of maximum cut. In addition, G contains no five-clique. The upper profile with these properties is still open here, as is the lower triangle-edge profile. [FixedCubics.lean](FixedCubics.lean) · [UpperClique.lean](UpperClique.lean)

## Counting on the two shores

The predecessor shows that every maximum cut splits H into equal shores, each high vertex has a strict majority of neighbors across the cut, and at most two high vertices have exactly two crossing neighbors. Each high vertex with two or more same-shore neighbors lies across an edge from one of these critical vertices.

Every high vertex has a distinct original triangle count at least two. If only one high vertex has two same-shore neighbors, each shore has fewer internal edges than vertices in every nonempty induced subset. An ordinary vertex x has at most one same-shore neighbor. Its incident triangles therefore come either from an edge among its opposite neighbors or from its single same-shore neighbor and an opposite neighbor. This bounds its score by |H|−1. The remaining |H|−1 ordinary vertices would need distinct values from 2 through |H|−1, which has only |H|−2 values. Thus each maximum cut has at least two vertices with two or more same-shore neighbors. [ShoreCounts.lean](ShoreCounts.lean)

Suppose all these vertices are confined to a pair on one shore. Each nonempty induced subset of either shore still has fewer edges than vertices. In the shore with no branching, the internal graph is a matching. An ordinary vertex of the other shore therefore has score at most |H|−2. An ordinary vertex in the matching shore can attain |H|−1 only if it and its same-shore mate are both adjacent to the entire opposite high shore. Their triangle counts would then coincide. This bounds every ordinary score by |H|−2; there are at least |H|−2 such vertices but only |H|−3 available values. A single critical cubic could cover at most its two crossing neighbors, both on one shore, so this excludes it. The two critical cubics necessarily have distinct scores in {2,3}, exhausting all cubic vertices. Adjacent cubics in the score-three vertex's four-clique would have equal scores. [ShoreRanks.lean](ShoreRanks.lean) · [FixedCubics.lean](FixedCubics.lean)

## Five-clique transfer

The earlier theorem CliquePivot33.three_cubics is independent of the order of the graph. It requires minimum degree at least three in the uncredited case, positive pairwise distinct triangle counts, and the inequality |V| ≤ 2|D| for every two-dominating set D. A five-clique then forces a cubic vertex of score one. Take the induced high subgraph J[H]. Every skeleton edge has both endpoints in H, its positive scores are retained, and each high score is at least two. Lifting feasible omissions from J[H] back to G proves the required domination inequality. Every five-clique of G lies in J[H]. The score-one conclusion gives a contradiction. This part of the proof works even when the high set is empty. [ShoreCliquePivot.lean](ShoreCliquePivot.lean) · [UpperClique.lean](UpperClique.lean)

## Exact source reuse

The transitively included leaf-stage source archive has SHA-256 d43ebb35933cb048eb6322e4e38c819a1d6c42db02ccb92beb2f83d3c441d8f1. It pins the 48-module nonleaf-zero predecessor. The six shore modules are listed in compilation order in replay_shore.py.

* ShorePairs extracts the unordered-pair definition, membership and insertion proofs from HighEarDegree33.lean, and the degree sum from SparseLink28.lean. The exact source files have SHA-256 e85310bb005bae3382cbf64e420490f3bbf8918794106d7605ab26389346ad4d and 12a85bb7409ff7da3b6f48f5e4a921869ca4e38dee388edf76e01236da94ce90.
* FixedCubics reuses the full_neighbors proof from CubicAnchor33.lean, SHA-256 8d9bf644872b234c44b3b89eb1af21aab520c75cfcd4c6f075cc72bd75b11061. Its fixed-pair and nonadjacency arguments are new here.
* ShoreCliquePivot extracts the full general CliquePivot33 namespace from CliquePivot33.lean, SHA-256 32b1862aa67fc77b9598db2f7fcc610e18c8ac6dc06d7631a23600c1650c696f. Its imports are reduced to the pinned Mathlib clique module, Prune384b and PinnedColor34_384b. The later order-33-specific namespace is outside the extracted block. The hypothesis transfer is explicit in UpperClique.

## Replay

From the extracted source archive run the following commands with the pinned Lean 4.19.0 binary and built Mathlib v4.19.0 source checkout.

~~~sh
export CROSSFOUR_LEAN_BIN=/absolute/path/to/lean-4.19.0-linux/bin
export CROSSFOUR_MATHLIB=/absolute/path/to/built/mathlib4
python3 -B replay_shore.py
~~~

The default cold command builds all 59 project modules. A segmented full replay runs the included predecessor's replay_leaf.py cold and then runs replay_shore.py --leaf-log /absolute/path/to/CompleteCold.log. This option authenticates all 53 predecessor object hashes and compiles the six shore modules from their exact sources. Both paths check all six expected object hashes, every axiom report, forbidden declarations and warnings as errors. No graph enumeration contributes to these theorems. [Entry point](replay_shore.py) · [Source hashes](SOURCES.sha256) · [Object hashes](OBJECTS.sha256)

[Complete pinned Lean sources](proof-sources.zip). Extract the archive and use its replay script.
