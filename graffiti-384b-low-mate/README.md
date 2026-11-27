# Graffiti.pc #384b with 29 triangle counts and a degree-two vertex adjacent to a low-degree vertex

**Let G be any finite simple graph of order n with 29 distinct vertex triangle counts and exactly 27 vertices of degree at least three. If a degree-two vertex has a neighbor of degree at most two, then γ₂(G) ≤ n − 15.** This settles the full pendant-triangle branch at every exposure. It also covers adjacent degree-two vertices with different other neighbors and a leaf adjacent to a degree-two vertex. The graph may be disconnected. [Graph-level theorems](LowMateClose.lean)

The catalogue counts the distinct numbers of unordered triangles incident to a vertex, including zero if it occurs. Every vertex outside a 2-dominating set must have at least two distinct neighbors inside it. At diversity 29 the conjectured inequality is equivalent to omitting at least 15 vertices. The previous pendant theorem at the same diversity required one of several degree or exposure conditions. [Ermelinda DeLaViña’s Graffiti.pc catalogue](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/index.html) · [Published #384b definitions and universal bound](https://github.com/vjdad4m/maths/tree/d7dc803dd2c9f038ba88bfc540430474dc63dd5b/graffiti-384b-partial) · [Previous exposure bounds](https://github.com/vjdad4m/maths/tree/d7dc803dd2c9f038ba88bfc540430474dc63dd5b/graffiti-384b-pendant-exposure)

## Why exposure is no longer required

Write e for a degree-two vertex with at most one high neighbor, where high means degree at least three. Reserve that high neighbor w, choosing any high vertex if e has none. The remaining 26 high vertices form X. There are no edges from e to X, so e can be omitted in any trial on X. The maximal-diversity identity 29 = 27 + 2 makes the triangle counts in X distinct and at least two.

**A five-clique inside X gives a deterministic cut.** If a clique pivot x can be omitted on both sides of a pinned cut, the two omission sets inside X together count 27 vertices with multiplicity. One set has at least 14, and e supplies the fifteenth. Only a cubic vertex adjacent to x can lose the third neighbor that made the cut argument work. A cubic vertex can be protected by pinning it opposite two other neighbors in the clique. [Cut with the permanent omission](PoolCut.lean)

There are at most two cubic vertices in X, since their distinct triangle counts belong to {2,3}. Suppose a five-clique fails to give the desired omission set. At each of its vertices the proof needs either a cubic neighbor seeing at most two clique vertices, or at least two cubic neighbors. Indeed, a sole cubic seeing three clique vertices can be protected by its other two clique neighbors. Give two units per contact to a cubic seeing at most two clique vertices, and one unit per contact otherwise. Each clique vertex then needs at least two units, but the two cubics supply at most four each. This excludes a five-clique inside X in any failure; the original graph can still contain five-cliques meeting the exterior. [Cubic contact count](PoolFive.lean)

**In the five-clique-free pool, sample ten vertices of X.** A vertex with no exterior neighbor has its entire neighborhood in X. That neighborhood contains no four-clique, so Turán’s theorem bounds its triangle count by the edge count of the balanced tripartite graph on its degree. An exposed vertex has one retained exterior neighbor and only needs one more. Summing the larger of the corresponding repair charges at each score rank covers any exposure pattern.

At zero-based rank one the score is at least three. An unexposed cubic at that rank has exactly three triangles and a clique neighborhood. The earlier trial can remove it when it is sampled and has two retained neighbors. If its degree is larger, its deficiency charge already drops. After this correction the total upper bound for deficiencies minus removable sample vertices is **15,680,531**. Failure on every ten-subset would give a lower bound of **3 × C(26,10) = 15,935,205**. The kernel checks the integer comparison and its rank-by-rank premises. [Turán and sampling proof](PoolRank.lean)

The pool theorem applies more generally to any set of 26 high vertices with distinct triangle counts at least two and an exterior vertex of degree at least two with no neighbor in that set. The graph-level corollary uses the two numerical catalogue hypotheses to obtain this pool.

## Exact remaining branch

Above the minimum quota, the earlier reduction gives either 29 nonleaves and two degree-two vertices or 30 nonleaves and three degree-two vertices. In any remaining failure all degree-two vertices are pairwise nonadjacent and each has two high neighbors. For every subset S of them, its union of neighbor sets has at least 2|S| − 1 vertices. Thus the two-ear case needs at least three distinct high anchors, and the three-ear case needs at least five. Across the whole ear family there can be at most one repeated anchor occurrence. Both disjoint anchor sets and a single shared anchor remain possible under the proved restrictions. The 28-nonleaf branch is separate. [Residual theorem](LowMateClose.lean) · [Predecessor quota reduction](https://github.com/vjdad4m/maths/tree/d7dc803dd2c9f038ba88bfc540430474dc63dd5b/graffiti-384b-one-degree-two)

## Reuse

The pinned-cut construction and weighted cubic contact argument adapt PivotQuota.paired and PivotQuota.seven_free. Those theorems require triangle diversity equal to the high count plus one. The new cut reserves e outside a 26-vertex pool and uses at most two cubics inside that pool. The local Turán argument adapts RankTuran.local_turan to neighborhoods wholly contained in X. The proof imports the rank sum, finite-range and boundary counts, and PendantRank.trial and its activation fiber from the frozen predecessor. Its third-ear and donor lemmas impose no hypotheses on this closure and the new proof needs only the zero-donor trial. The residual uses Remaining29.residual and Repair.exact_of_low_support. [Earlier clique pivot](https://github.com/vjdad4m/maths/blob/d7dc803dd2c9f038ba88bfc540430474dc63dd5b/graffiti-384b-one-degree-two/QuotaPivot.lean) · [Earlier cubic count](https://github.com/vjdad4m/maths/blob/d7dc803dd2c9f038ba88bfc540430474dc63dd5b/graffiti-384b-one-degree-two/QuotaClique.lean) · [Sampling and activation predecessor](https://github.com/vjdad4m/maths/tree/d7dc803dd2c9f038ba88bfc540430474dc63dd5b/graffiti-384b-pendant-exposure)

## Strict replay

From this directory in the shared workspace run

```sh
python3 -B replay.py --checked ../graff384b-pendant-ranks/StrictRanks.log
```

Lean 4.19.0 commit 6caaee842e94 and Mathlib v4.19.0 commit c44e0c8ee63ca166450922a373c7409c5d26b00b are pinned. The replay checks the frozen predecessor archive, its delivery manifest, its original transcript, and 187 compiled-object hashes. It rebuilds four modules with warnings as errors and synchronous elaboration, checks all six named axiom reports, and permits only propext, Classical.choice and Quot.sound. [Transcript](StrictClosure.log) · [Replay script](replay.py) · [Source hashes](NEW-SOURCES.sha256)

For a cold rebuild after extracting the source archive, run the following from its source directory. The source closure includes its predecessor archive recursively.

```sh
CROSSFOUR_LEAN_BIN=/absolute/path/to/lean-4.19.0-linux/bin \
CROSSFOUR_MATHLIB=/absolute/path/to/mathlib4-4.19.0 \
python3 -B replay.py --cold
```

The workspace and extracted-package replays used the checked-predecessor mode. The full predecessor chain was not cold-rebuilt for this delivery.

[Complete pinned Lean sources](proof-sources.zip). Extract the archive and use its replay script.
