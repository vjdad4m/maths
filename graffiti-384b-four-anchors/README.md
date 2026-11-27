# Graffiti.pc #384b with four distinct ear neighbors

Let G be a finite simple graph with 29 distinct vertex triangle counts, 29 vertices of degree at least two, and 27 vertices of degree at least three. Write e and f for the two degree-two vertices, W for their four distinct high neighbors, and X for the remaining 23 high vertices. The target is γ₂(G) ≤ |V(G)| − 15. The published shared-anchor theorem already handles repeated neighbors. All results below allow disconnected graphs. [Official Graffiti.pc catalogue, Ermelinda DeLaViña](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/index.html) · [Frozen shared-anchor theorem and profile](https://github.com/vjdad4m/maths/tree/7d2af907520e1df2e80b5d30d7238101560bec0f/graffiti-384b-shared-anchors)

Define three counts on X.

- T counts vertices that occur in a triangle together with some anchor in W.
- M counts vertices that have at least one neighbor outside X.
- D counts vertices that have at least two neighbors outside X. All exterior vertices are retained initially, so even an adjacent leaf supplies a contact.

**The catalogue bound holds if T ≤ 3 or M ≥ 15. It also holds if M ≥ 14 and D ≥ 7, or M ≥ 13 and D ≥ 11.** Thus every remaining failure satisfies 4 ≤ T ≤ M ≤ 14, with D ≤ 6 at M = 14 and D ≤ 10 at M = 13. The implication T ≤ M follows because every vertex counted by T has an adjacent anchor. [Graph-level dense theorem](FourProfile.lean) · [Sparse theorem and failure restrictions](FourFront.lean)

## A protected cut from nine vertices

Choose the four anchors, up to three further high vertices containing all triangle partners of the anchors outside W, and the two ears. Pad the three high positions with other vertices in X if necessary. At every anchor each triangle partner is either high or a degree-two vertex. Consequently the anchor scores in this induced graph agree with their scores in G. The extremal diversity identity 29 = 27 + 2 gives four distinct scores, each at least two.

There are 21 possible edges among the seven high labels. The ear edges are fixed. For each assignment of those 21 edges, put each ear opposite both of its anchors. Up to global reversal, there are two relative orientations of the two anchor pairs. Each of the other three high labels can be pinned to either side or left free. Lean checks all 2²¹ edge assignments against these 54 placements. Whenever the four anchor counts are distinct and at least two, some placement gives every pinned vertex at least two neighbors pinned opposite. All unpinned nonleaves have degree at least three. The earlier pinned maximum-cut theorem extends this placement and gives the desired domination bound. [Finite table](LocalTable.lean) · [Translation to graph edges and triangles](SignalSemantics.lean) · [Cut theorem](ProtectedNine.lean)

The finite calculation stores all assignments in natural-number bit positions. The correspondence between a graph and its assignment, the triangle counters, and the interpretation of each placement are proved in Lean. The final table equality is proved by reflexivity and reports only `propext`. The reusable theorem `LocalTest.nine_induced` applies whenever *any* choice of three extra vertices gives four distinct induced anchor counts at least two. It can therefore certify graphs with more than three triangle contacts as well. [Word lemmas](TruthWords.lean) · [Placements and adjacency encodings](LocalSignals.lean)

## Eight-vertex samples and four missing ranks

Sample eight of the 23 pool vertices and keep all exterior vertices initially. Remove both ears and every eligible sampled vertex whose neighbors form a clique. Each ear has both neighbors retained. Removing the second ear preserves the deficient set. If all samples fail to reach fifteen omissions, the total deficiency exceeds the total number of removable sampled vertices by at least 3·C(23,8) = 1,470,942. One fixed exterior neighbor cuts the deficiency estimate to a zero-hit count. Two fixed neighbors make it zero. A simplicial vertex at a saturated score rank earns a further saving. The three dense conditions beat the failure threshold by 3,392, 10,542, and 16,262 respectively. [Two fixed ear omissions](FourTrial.lean) · [Finite repair estimates](DenseFour.lean)

Four reserved scores also give conditional bounds in the middle range. Each column below suffices for the catalogue inequality. The first row is a lower bound on M and the second is an upper bound on all four anchor triangle counts.

| Minimum M | 0 | 4 | 6 | 9 | 10 | 11 | 12 | 13 | 14 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Maximum anchor score | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 15 |

If the four anchor scores are at most s, the score at zero-based pool rank i is at least i + 6 once s ≤ i + 5. The rank proof uses injectivity over all 27 high vertices. The theorem `four_missing_rows` also gives a necessary repair inequality using each anchor’s actual global rank, for arbitrary nonnegative prices on single and double exposure. [Four-rank accounting and threshold table](FourRankGap.lean)

A checked arithmetic example identifies a limit of this estimate. Reserve ranks 23 through 26, assign exactly one exterior contact to each of retained ranks 15 through 22, and use zero for every other contact. The envelope exceeds the target by at least 359,828 over all exposure prices in this eight-seed estimate. This establishes a limitation of the counting bound. Graph realizability of that numerical profile remains undetermined. The general four-anchor branch and the catalogue conjecture remain open. [Numerical obstruction](FourRankGap.lean)

## Provenance and verification

The extension uses the triangle, two-domination, and rank definitions in the published predecessor. It reuses its zero-hit boundary estimate, sampled clique-neighborhood removal theorem, and retained-neighbor deletion lemma. The two-ear trial is adapted to a 23-vertex pool, which fails the earlier cut-balance hypothesis. The graph-level disjointness and score injectivity come from the predecessor’s failure reductions. The protected-placement argument invokes `PinnedColor34.complete` on the original graph. [Published predecessor at 7d2af907](https://github.com/vjdad4m/maths/tree/7d2af907520e1df2e80b5d30d7238101560bec0f/graffiti-384b-shared-anchors)

From the scratch source directory, replay with

```sh
python3 -B replay.py --checked ../graff384b-shared29-astra/StrictShared.log
```

Lean 4.19.0 commit 6caaee842e94 and Mathlib v4.19.0 commit c44e0c8ee63ca166450922a373c7409c5d26b00b are pinned. The replay checks all 206 Lean source hashes and 196 predecessor object hashes, builds the ten new modules with warnings as errors and synchronous elaboration, and audits twenty axiom reports against `propext`, `Classical.choice`, and `Quot.sound`. [Strict replay](StrictFour.log) · [Replay script](replay.py)

The archive includes all transitive project sources. For a cold build, enter the extracted directory containing `replay.py` and run

```sh
CROSSFOUR_LEAN_BIN=/absolute/path/to/lean-4.19.0-linux/bin \
CROSSFOUR_MATHLIB=/absolute/path/to/mathlib4-4.19.0 \
python3 -B replay.py --cold
```

The workspace and extracted-package runs used the checked-predecessor mode.

[Complete pinned Lean sources](proof-sources.zip). Extract the archive and use its replay script.
