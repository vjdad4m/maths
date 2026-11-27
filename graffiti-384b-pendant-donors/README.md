# Graffiti.pc #384b at 29 triangle counts and 27 high vertices

A pendant triangle with two degree-two vertices gives a 2-dominating set of size at most **n − 15** in each of the three regimes below. Here n is the order of a finite simple graph, exactly 29 different numbers of triangles through a vertex occur, and exactly 27 vertices have degree at least three. The proof permits disconnected graphs and arbitrary numbers of leaves and isolated vertices. [Main theorem](PendantDonor.lean) · [Degree-five corollary](RootContact.lean)

Let u,v be the degree-two vertices, with N(u) = {v,w} and N(v) = {u,w}, where w has degree at least three. Let X be the other 26 vertices of degree at least three. Write e for the number of vertices in X with a neighbor outside X. Each such vertex counts once, regardless of how many exterior neighbors it has. It suffices that any one row holds.

| Minimum degree in X | Required e | Sample size |
| --- | ---: | ---: |
| 3 | 14 | 9 |
| 4 | 12 | 9 |
| 5 | 1 | 10 |

**When at most 30 vertices have degree at least two, the last row needs only the degree assumption.** A vertex w without any high neighbor uses two distinct degree-two vertices for each triangle through it. The link-degree sum proves this without an assumption on the rest of the graph. At the present diversity w lies on at least two triangles, and the nonleaf quota allows at most three degree-two vertices. Hence w has a neighbor in X, and that vertex counts toward e. This applies to both residual nonleaf counts, 29 and 30. [Formal counting argument](RootContact.lean)

The conjecture asks for γ₂(G) ≤ n − ⌈t/2⌉, where t counts distinct triangle-incidence values, including zero when present. An outside vertex must have at least two neighbors in the chosen set. The preceding reduction leaves 27 high vertices in both above-minimum residual profiles. Its sparse spanning graph preserves the triangle counts and the high and nonleaf sets. The present theorem can be applied on that spanning graph whenever its pendant triangle and the stated degree and exposure condition hold. [Ermelinda DeLaViña’s Graffiti.pc catalogue](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/index.html) · [Published definitions](https://github.com/vjdad4m/maths/blob/e7fc7016f64828213df38f8675c795d6dfd13889/graffiti-384b-partial/src/Proof384b.lean) · [Previous single-ear and sparse-star reduction](https://github.com/vjdad4m/maths/tree/e7fc7016f64828213df38f8675c795d6dfd13889/graffiti-384b-one-degree-two)

## Why the sample exists

Fix all vertices outside X except u and v. For a b-subset k of X, let s consist of the fixed vertices together with k, and B(s) consist of all vertices outside s with fewer than two neighbors in it. In every trial w belongs to s and u,v each have exactly one neighbor in s. If the usual repair adds both, retaining v alone already gives u its second neighbor. The problem is to find a trial that also meets the raw size budget.

On X the 26 distinct triangle counts are at least two. Count the unsampled deficient vertices rank by rank using the degree lower bounds from the binomial triangle cap. An exterior contact gives the sharper zero-hit bound. Both ears have no neighbor in X, so these counts are valid even when the ears are absent. The strict integer comparisons prove the existence of k with |k| plus its deficient count in X at most 12. The table records the upper and lower sides of the contradiction obtained by assuming every k fails. The exposure price is an auxiliary integer used to sum the two per-vertex estimates. [Kernel-checked rank calculation](PendantBudget.lean)

| b | Degree floor | e | Exposure price | Rank sum | Strict threshold |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 9 | 3 | 14 | 377910 | 17538628 | 17788940 |
| 9 | 4 | 12 | 262548 | 15456604 | 15648776 |
| 10 | 5 | 1 | 170170 | 16042390 | 16105375 |

The resulting s satisfies |s| + |B(s)| ≤ n − 14 and has the specified usable pair. The repair produces γ₂(G) ≤ n − 15. At q = 29 or 30, a possible failure with this pendant triangle must therefore have e ≤ 13, some vertex of X of degree at most four, and either e ≤ 11 or a cubic vertex in X. Other attachment patterns and the pendant cases still meeting these restrictions remain open here.

## Oriented-pair counts at any diversity

For a fixed seed set F disjoint from a pool X, sample b vertices of X. The exact contribution of a vertex to the total number of deficient vertices over all trials is computed from its contacts with F and with X minus that vertex. Summing these contributions gives the total raw repair count L. The fixed-donor theorem also handles multiple permanently deficient recipients with shared donors. [Exact losses](ConditionalMass.lean) · [Fixed donors](ForcedDonors.lean)

For a specified edge uv with u excluded from F and X, let I count the trials in which u has one seed neighbor and v is deficient. If L < (cap + 1) · C(|X|,b) + I, some trial either meets the raw cap, or exceeds it by one with that usable pair. In either event γ₂ ≤ |F| + b + cap. This counts the discount in the same trials as the raw charges. The theorem allows the donor v to be sampled in other trials. [Averaged discount and existence theorem](EdgeDiscount.lean)

For zero fixed seeds and both endpoints excluded, partition X into a neighbors only of u, d neighbors only of v, c common neighbors, and o neighbors of neither. The exact I for k seeds is

`(a + c) · C(o,k − 1) + a · d · C(o,k − 2)`,

with a zero term at an invalid binomial index. The separate zero- and one-seed lemmas handle the truncated natural subtraction at the lower end. When there are fixed contacts, conditioning on the unique neighbor of u gives a sum of exact donor losses if u has zero fixed neighbors. With one fixed neighbor, only the pool of nonneighbors of u may be sampled. With two or more, the event is impossible by monotonicity. The file proves the two positive-count formulas. [Conditional formulas](EdgeMass.lean) · [Four-class formula and small samples](FourClasses.lean)

## Reuse and attribution

* The reviewed pair and batch repair sources match the [published versions](../graffiti-384b-discounted-repairs/) byte for byte and are not duplicated here. The published maximum-cut repair theorem is complementary. [Published discounted repairs](https://github.com/vjdad4m/maths/tree/e7fc7016f64828213df38f8675c795d6dfd13889/graffiti-384b-discounted-repairs)
* The existing EarAnchor34.balance credits a permanently retained pendant root in a diversity-33 sampling obstruction. The present work establishes actual critical-budget samples in the three diversity-29 regimes above. It reuses Repair.maximal_diversity, RankStrata.hits, JointRank.rank_lower and sum_by_rank, FiniteRange.count_bad, BoundaryFiber.count, and Repair.link_sum. [Earlier ear sampling](https://github.com/vjdad4m/maths/tree/e7fc7016f64828213df38f8675c795d6dfd13889/graffiti-384b-two-ears)
* Graffiti.pc #180’s pair_of_bridge_ports addresses irredundant certificates and exchanges across a bridge; its hypotheses and conclusion differ from 2-domination. Its role here was conceptual. The recent ear-square theorem concerns 28 nonleaves. [#180 controlled exchanges](https://github.com/vjdad4m/maths/tree/e7fc7016f64828213df38f8675c795d6dfd13889/graffiti-180-controlled-pair-exchanges) · [28-nonleaf ear-square results](https://github.com/vjdad4m/maths/tree/e7fc7016f64828213df38f8675c795d6dfd13889/graffiti-384b-core28-ear-squares)

## Replay

Use Lean and Mathlib v4.19.0, Mathlib pinned at `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Build the [single-ear predecessor](../graffiti-384b-one-degree-two/) and the [published repair lemmas](../graffiti-384b-discounted-repairs/) and their documented dependencies. Keep the objects and pinned Mathlib on the Lean search path. Check `sha256sum -c NEW-SOURCES.sha256` and compile the eight extension sources in `modules.txt` order with synchronous elaboration and warnings as errors. The [recorded archive replay](PackedReplay.log) rebuilt those eight modules and the two unchanged repair modules after matching 171 dependency object hashes. It reports only `propext`, `Classical.choice` and `Quot.sound` for 15 declarations. No recursive cold replay was recorded.
