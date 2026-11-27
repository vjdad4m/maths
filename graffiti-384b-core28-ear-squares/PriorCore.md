# Graffiti.pc #384b with 29 triangle counts and 28 nonleaves

The catalogue asks for a 2-dominating set of size at most `n − 15` when there are 29 distinct vertex triangle-incidence counts. A 2-dominating set gives every omitted vertex at least two distinct neighbors in the set. A nonleaf here has degree at least two. This package concerns graphs with exactly 28 nonleaves. The nine modules in the preceding diversity-29 release are preserved in their original archive. [Checked-result index](https://github.com/vjdad4m/maths/blob/main/README.md)

## The fifteenth omission

Let `H` be the graph induced by the 28 nonleaves. **If the vertices of H can be divided into two nonempty sets with no triangle meeting both, the original graph has a 2-dominating set of size at most n − 15.** Edges outside triangles may cross the division. The statement holds at every original graph order, with or without a connectivity assumption. This settles every even subdivision left by the previous parity theorem. [Original-graph theorem `exact_of_split`](CoreFrontier28.lean)

In a hypothetical failure let `J` be the spanning subgraph of `H` retaining just the edges in triangles. The previous release shows that all 28 vertices of `H` have positive, pairwise distinct triangle counts and that `γ₂(H) = 14`. The new reduction gives the following additional conditions.

- `J` is connected, `γ₂(J) = 14`, and `J` contains a four-clique. Exactly one vertex has degree two in `J`. Its two neighbors are adjacent, and it has triangle count one in `H`.
- If `J` has no five-clique, at least five of the six counts 1 through 6 occur, including 1.
- If `J` has a five-clique, its cubic vertices of counts 2 and 3 both exist. At least three vertices of every five-clique belong to the union of their neighborhoods. Each five-clique meets the neighborhood of the score-three cubic, and the cubics have at most one common neighbor. Their degrees and contacts are measured in `J`. [Core and original-graph theorems](CoreFrontier28.lean) · [Five-clique branch](SharedFrontier28.lean)

**Two shared neighbors suffice even without a five-clique hypothesis.** Whenever the triangle-edge graph of the nonleaf core contains a score-two cubic and a score-three cubic with at least two common neighbors, the original graph has a 2-dominating set of size at most n − 15. [Original-graph theorem `exact_of_shared_pair`](SharedFrontier28.lean)

The original case is still open when the connected triangle-edge graph satisfies these restrictions. The cases with 29 or 30 nonleaves retain the previous release's bounds.

## Why two triangle components give a saving

The half-order bound for a graph with distinct positive triangle counts applies separately to each triangle-closed side after removing triangle-free edges. Equality for the whole graph forces equality on both sides, preserves each individual count, and forces both side sizes to be even. A nonempty such side has at least six vertices. For smaller even sizes there are too few distinct positive counts, since at order `k` each is at most `C(k−1,2)`. [Equality and score preservation](ShoreEquality28.lean) · [Size reduction](ShoreFinish28.lean)

If a side has a five-clique, all three counts 1, 2 and 3 occur on that side. With an ear this follows from the order-independent `ThirtyCore.both_required`. With minimum degree at least three it follows from `CliquePivot33.three_cubics`. A five-clique-free half-tight side of even order 6 through 28 also needs at least one of those three counts. For this last assertion, a uniform sample followed by including deficient vertices gives an inequality, and the tripartite Turán bound for each neighborhood supplies the degree required by each rank. If the smallest score is at least four, the inequality fails. Since the two sides have disjoint scores, a five-clique on either side is impossible. [Five-clique argument](ShoreEquality28.lean) · [Sampler at every even side size](ShoreSample28.lean)

With both sides five-clique-free, rank all 28 scores together. For a side of order `k` choose a sample of `b` vertices. A vertex with degree at least `d` is omitted and sees fewer than two sample vertices in at most `C(k−1−d,b) + d C(k−1−d,b−1)` samples. If the 2-domination number on the side is `k/2`, the total number of such failures over all samples is at least `C(k,b)(k/2−b)`. Each side has its own sample size and price in the following table. The price is a positive integer multiplier for its inequality. The left shift is added to each rank assigned to the smaller side. Lean verifies the strict contradiction for every allocation of the 28 ranks compatible with the two side sizes and degrees.

| Side sizes | Sample sizes | Prices | Left shift | Maximum joint charge | Required charge |
| --- | --- | --- | ---: | ---: | ---: |
| 6 and 22 | 2 and 8 | 21,318 and 5 | 546,924 | 7,242,084 | 8,397,864 |
| 8 and 20 | 3 and 7 | 7,752 and 7 | 84,084 | 2,487,791 | 2,734,704 |
| 10 and 18 | 3 and 6 | 26,299 and 200 | 106,400 | 17,618,468 | 18,514,160 |
| 12 and 16 | 4 and 6 | 2,912 and 225 | 10,052 | 5,981,051 | 6,607,104 |
| 14 and 14 | 5 and 5 | 1 and 1 | 0 | 6,991 | 8,008 |

The charge column is an upper bound obtained by maximizing each rank's contribution separately after the shift. The proof does not assume a proposed assignment of ranks is realizable. The graph-to-table link uses injectivity, coverage of all 28 ranks, and the neighborhood Turán bound. [Five-row certificate](ShoreSplitBudget28.lean) · [Graph-to-rank proof](ShoreFinish28.lean)

## What remains inside one component

For a four- or five-clique-free 28-vertex graph, let `A` be its realized positive scores at most six. At degree `d`, a score bounded by `c` can occupy only the elements of `A` up to `c` and the integers 7 through `c`. This improves the degree bound on each rank. A ten-vertex sample rules out every four-clique-free profile and every five-clique-free profile missing count 1 or realizing at most four of the first six counts. Lean checks both clique bounds and all 64 subsets of the first six positive integers. The unique score-one vertex has exactly two neighbors after trimming. [Rank and local-density certificate](CorePalette28.lean) · [Ear theorem](CoreFrontier28.lean)

In the five-clique case, suppose the two forced cubics share two neighbors. The published transversal theorem implies that every five-clique contains one of the two neighbors. Retain both and omit both cubics. Sample nine of the remaining 24 vertices. The unrestricted rank estimate would charge 3,949,722 failures over all samples. The third neighbor of the score-three cubic is a genuine exterior vertex adjacent to both retained neighbors. It never needs repair, removing at least 29,029 from the charge. This leaves at most 3,920,693, strictly below `3 C(24,9) = 3,922,512`. Some sample therefore needs at most two repairs. The resulting 2-dominating set has at most `2 + 9 + 2 = 13` vertices in `J`, which rules out this branch. [Protected-vertex accounting](ProtectedFiber28.lean) · [Witness construction](ProtectedPair28.lean) · [Application to the original graph](SharedFrontier28.lean)

