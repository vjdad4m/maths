# Graffiti.pc #384b at 31 nonleaves and 31 distinct triangle counts

Let G be a finite simple graph on n vertices. Write γ₂(G) for the smallest cardinality of a vertex set in which each outside vertex has at least two neighbors. Suppose exactly 31 vertices have degree at least two, and the numbers of triangles incident to individual vertices take exactly 31 distinct values. The #384b inequality at this diversity is γ₂(G) ≤ n − 16. All results below allow arbitrary order, isolated vertices and disconnected graphs. [Ermelinda DeLaVina's Written on the Wall II catalogue](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/index.html)

**The shared-neighbor case is closed.** If two distinct degree-two vertices share a neighbor, G satisfies the inequality. The frozen predecessor proves that any failure at these quotas has exactly two degree-two vertices (the ears) and 29 vertices of degree at least three (the high vertices). All four ear-neighbor incidences land among the high vertices. The new theorem therefore forces the two ears to have four distinct neighbors in any remaining failure. [Original-graph proof](SeparatedAnchors.lean) · [Predecessor](../graffiti-384b-low-ear/)

**Four distinct neighbors.** Denote the four neighbors by A and the other 25 high vertices by X. Write m for the number of vertices of X adjacent to at least one member of A, and b for the number adjacent to at least two. A failure satisfies all three conclusions below.

1. We have m ≤ 14. If m = 14 then b ≤ 5, and if m = 13 then b ≤ 9. [Original-graph theorem](FourFrontier.lean)
2. Some member of A has no neighbor among those b vertices. Every neighbor it has in X thus touches exactly one member of A. [Protected-cut proof](AnchorCuts.lean)
3. Some member of A has no neighbor in the other ear's pair of anchors. The vertex witnessing this conclusion can differ from the one in the previous conclusion. [Cross-edge proof](AnchorCuts.lean)

These are necessary conditions on a hypothetical counterexample. The four-distinct-neighbor case subject to these restrictions remains open in this package.

## Proof details

When just three high neighbors a, b, z support both ears, fix all three in the 2-dominating set and omit the ears. Here z is their common neighbor. Failure would force the exterior anchors a and b to have no common neighbor other than possibly z, by the predecessor's outer-separation theorem. Thus their respective neighbor counts x and y in the pool of 26 remaining high vertices satisfy x + y ≤ m, where m counts pool vertices touching any of the three anchors. At a and b there is at most one triangle through an ear and at most one further exceptional triangle, with vertices a, b, z. The triangle counts at a, b, z are therefore bounded by 2 + C(x+1,2), 2 + C(y+1,2), 2 + C(m+2,2). Equal neighbor pairs are already covered by the existing twin-ear theorem. [Triangle-count bound](OuterScore.lean) · [Graph reduction](SeparatedAnchors.lean)

Sample nine of the 26 pool vertices. With at least ten contacts the existing ranked neighbor estimate excludes failure. With at most nine, rank all 29 high vertices and use the three triangle bounds to account for the ranks occupied by the fixed anchors. For each sample one can omit both ears and any eligible sampled vertices with clique neighborhoods. Over all samples failure would require net deficiency at least 4 C(26,9) = 12,498,200. The low-contact rank table excludes this with integer margin at least 79,633. [Finite inequalities and counting proof](Pool26.lean)

With four fixed anchors, only eight of the other 25 high vertices are sampled. An omitted ear is always supported by its two fixed anchors. A sampled cubic vertex of triangle count two can also be omitted whenever the two endpoints of the path in its neighborhood are retained. This gives at least C(22,5) = 26,334 qualifying samples. A pool vertex touching two anchors never needs repair. Summing the costs at two choices of weight gives 160,000m + 24,310b ≤ 2,373,500 and 160,000m + 43,758b ≤ 2,490,188. These bounds pay for all four fixed anchors and imply the first conclusion. [Sampling and simultaneous cubic saving](FourSample.lean) · [Both sums](FourPrices.lean)

For the second conclusion, put the ears and the b vertices on one side of a cut and the four anchors on the other. If all four anchors touched the b vertices, each anchor would see both its ear and another vertex across the cut. Every vertex on the first side already sees two anchors. This contradicts the earlier protected-cut theorem because both ears belong to the cut. For the third conclusion put each ear on the same side as the other ear's neighbor pair. If every anchor met the opposite pair, the same contradiction would follow. [Both cut certificates](AnchorCuts.lean)

## Replay

With Lean 4.19.0 and pinned Mathlib v4.19.0, compile the dependencies of the [low-degree-ear package](../graffiti-384b-low-ear/) and [adjacent-ear package](../graffiti-384b-adjacent-full/) first, with their objects on the Lean search path (direct imports: `OuterSeparation`, `CubicSaving`, `CliquePool`). Compile each source in `modules.txt` order with `-DElab.async=false -DwarningAsError=true`, making the prior objects accessible. See the [recorded strict replay](StrictAnchorPairs.log) and [exact source hashes](NEW-SOURCES.sha256). The full conjecture remains unresolved.
