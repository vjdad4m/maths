# Graffiti.pc #384b with at most seven exterior contacts

Let G be a finite simple graph with exactly 31 vertices of degree at least two and exactly 31 distinct values of the number of triangles through a vertex. At this diversity the conjectured bound is γ₂(G) ≤ |V(G)| − 16. A 2-dominating set provides at least two neighbors to each vertex outside it. The results here allow every order and disconnected graphs. [Ermelinda DeLaVina's Graffiti.pc catalogue](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/index.html)

**The bound holds when at most seven exterior high vertices touch an ear neighbor.** The predecessor gives exactly two degree-two vertices e,f in a potential failure. Their neighbor pairs are disjoint and consist of four high vertices, called the anchors A. A high vertex has degree at least three. Let X be the other 25 high vertices, and count in m each vertex of X touching A once. The new result covers m ≤ 7. [Direct domination theorem](AnchorGap.lean) · [Predecessor](../graffiti-384b-anchor-pairs/)

**Remaining contact restrictions.** A failure has 8 ≤ m ≤ 14. There is an anchor w such that every neighbor of w in X touches precisely one anchor and the graph induced by those neighbors has maximum degree at most one. Let x be their number. The new restrictions are

| Hypothesis | Necessary condition |
| --- | --- |
| Every such failure, for the chosen w | m ≥ x + 5 |
| x ≤ 3 | m ≥ x + 6 |
| x ≤ 1 | m ≥ x + 10 |
| x ≤ 3 and m < x + 10 | No triangle through w lies wholly in A, and its triangle count is at most 1 + ⌊x/2⌋ |

The matching-neighborhood anchor comes from the published ForkGuard34 theorem. A separate cut gives an anchor missing the other ear's pair. The new graph proof chooses each witness using its own existence theorem. [Original-graph restrictions](SparseFrontier.lean)

**At m = 8**, x = 2. Exactly two triangles meet w. One is formed by the ear incident to w and its other anchor. The other is formed by the two private exterior neighbors of w, which must be adjacent. Every other anchor has triangle count at least 15. The score gap holds whenever any anchor has triangle count two under the 31/31 quotas. [Eight-contact triangle characterization](SparseEight.lean) · [Score gap](AnchorGap.lean)

The restrictions leave open the eight-contact configuration just described and cases with more contacts. The proof supplies neither a graph violating the inequality nor a resolution of the whole 31-nonleaf profile.

## Proof

1. Sample eleven vertices uniformly from all 29 high vertices. The other vertices are initially retained. Omit an ear whenever both of its neighbors are sampled. An unsampled anchor can thus count its incident ear as a retained neighbor during repair. Sum the deficiency counts and the savings from sampled vertices with clique neighborhoods and from the cubic vertex of triangle count two. The proof ranks all 29 triangle counts and checks the integer costs for each possible rank and truncated degree. After the guaranteed ear omissions the four anchor savings can total at most 12,407,000 in a failure. [Sample count](SparseMass.lean) · [Rank and degree tables](SparseRanks.lean)
2. A score-two anchor saves at least 3,124,550 further trials. At degree at least four the original deficiency count gives the saving. At degree three its neighbors induce a path, and its ear is one endpoint. Sample the anchor and the other endpoint while omitting the middle from the sample. On each such trial the ear is ineligible for omission, so it can be retained while the anchor is omitted. The other ear and all the previous simultaneous savings are accounted for. There are C(26,9) = 3,124,550 such eleven-vertex samples. Together with the ordinary anchor credits this gives the score gap. [Sample-dependent replacement](SparseSwap.lean) · [Graph-level saving](SparseCubic.lean)
3. Count triangles through each anchor according to whether their other vertices belong to its exterior row, the four anchors, or one of each. At most one triangle is wholly among the four anchors, because at least one has at most one neighbor in A. The exterior row of the selected private anchor is a matching with possible isolated vertices, so it contributes at most ⌊x/2⌋ triangles and has no mixed triangles. Applying the rank costs, including the actual degree of w, forces at least five contacts outside its row. The distinct triangle counts of the three other anchors give the six-contact strengthening. [Triangle counts](SparseGeometry.lean) · [Rank deductions](SparseFrontier.lean)
4. Suppose x ≤ 3 and w lies on a triangle of anchors. If at most nine exterior contacts lie outside w's row, the other ear's two anchors must have a common exterior neighbor. Otherwise each needs at least five separate exterior contacts to meet the necessary triangle count. The existing four-cycle contact theorem then precludes a second such cycle through the first ear. This forces w to see both anchors c,d of the other ear and its mate b to see neither. No edge can go from an exterior neighbor of b to a common exterior neighbor of c and d, since such an edge completes a cut protecting both ears. Let T be that set of common neighbors and S the neighbors of b outside T. Only vertices of S can form an all-high triangle with b. With j = m − x we have |S| + |N(c)∩X| + |N(d)∩X| ≤ 2j. The score constraints imply |S| ≥ 6 and each of the other two sizes is at least five. A checked finite table at j ≤ 9 now exceeds the available rank budget. This yields the ten-contact and the no-triangle conclusions. [Eight-vertex cut](AlternatingGuard.lean) · [Contact and rank calculation](PrivateContacts.lean)

## Strict replay

Use Lean 4.19.0 and pinned Mathlib v4.19.0. Build the [anchor-pairs package](../graffiti-384b-anchor-pairs/) and its dependency closure first, adding their objects to the search path. Compile the ten new modules in `modules.txt` order with `-DElab.async=false -DwarningAsError=true`. The recorded replay rechecked the predecessor objects and eighteen theorem reports, all with only standard axioms. Source digests and the original strict replay are included.
