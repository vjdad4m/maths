# Graffiti.pc #384b with 29 triangle counts and 28 nonleaves

Let `G` be a finite simple graph with exactly 29 distinct vertex triangle-incidence counts, including zero when realized, and exactly 28 vertices of degree at least two. Let `H` be induced by these 28 vertices. In a hypothetical failure its counts are positive and pairwise distinct. Write `J` for the spanning subgraph of `H` retaining its triangle edges. The previous nine-module release proves that `J` is connected, has 2-domination number 14, contains a four-clique and has a unique degree-two vertex `e` with adjacent neighbors `p,q`. Here assume that `J` has no five-clique. All subsequent degrees, counts and neighborhoods refer to `J`. A 2-dominating set gives every omitted vertex two distinct neighbors in the set. [Connected-core predecessor included here](PriorCore.md) · [Checked-result index](https://github.com/vjdad4m/maths/blob/main/README.md)

## Exact original-graph results

Suppose `s ≠ e` is another common neighbor of `p,q`, so that `e,p,s,q` form a four-cycle. **The original graph has a 2-dominating set of size at most `|V(G)| − 15` if any of the following holds.**

- The triangle count of `s` is two.
- The degree of `s` is three.
- The degree of `s` is four and its triangle count is three or five.
- The degree of `s` is four and `s` is the only common neighbor of `p,q` other than `e`.

These statements apply at any original graph order. The proof checks the catalogue bound with this triangle count diversity and imposes no connectivity premise on `G`. [Theorems `exact_low_square` and `exact_lone_quartic`](FourFrontier28.lean)

If a degree-four `s` survives, its triangle count equals four. Its neighborhood consists of `p,q,x,y`. The vertex `x` misses both ear neighbors and sees `y`. The vertex `y` sees both ear neighbors. Thus there are at least two different fourth vertices on ear squares. A surviving configuration then has cubic vertices of counts two and three outside both the ear triangle and the same induced copy of the five-clique minus one edge. [Theorem `quartic_frontier`](FourFrontier28.lean)

## Where the adjacent-deficit repair saves a vertex

Retain `p,q` and omit `e,s`. Sample nine of the remaining 24 vertices. Among these vertices a neighbor of `s` that sees neither retained neighbor can lose one unit of degree with no compensating support. At score two, the edge from `s` to each such neighbor belongs to the second triangle through `s`. The first triangle is `s,p,q`. Consequently there is at most one such neighbor, or exactly two that are adjacent. [Triangle classification](FourLowSquare28.lean)

When the second case occurs, call the two vertices `x,y` and measure their residual degrees after deleting `e,s`. The total number of deficient vertices, counted over all nine-vertex samples, is at most **3,651,882** plus a charge for each of `x,y`. The charge is 155,040 through degree four and 97,240 above degree four. Three deficits per sample would require **3,922,512** in total. If either degree exceeds four, the upper bound is 3,904,162. When both degrees are at most four, separately promoting every deficit gives a bound of 3,961,962 and misses by 39,450. [Rank-and-fiber bound `square_mass`](FourSquareSample28.lean)

Put `U=N(x)∪N(y)` in the residual graph. Both neighborhoods lie in the 24-vertex pool. Select exactly one vertex of `U∖{x,y}` and eight from outside `U`. Both `x,y` are absent and deficient. At least one already sees the selected vertex, so retaining the other supplies its second neighbor. With `m=|U|`, these are `(m−2) C(24−m,8)` distinct samples. Here `3≤m≤8`, giving **at least 77,220** samples on which the repair saves a vertex. The total saving exceeds 39,450. This comparison forces a sample with at most two net repairs and gives a 2-dominating set of size at most 13 that retains both ear neighbors. [Sample injection and set construction](FourPairRebate28.lean) · [Threshold argument](FourPairSample28.lean) · [Lift through the two omitted vertices](FourSquareSaving28.lean)

The [general repair lemmas](../graffiti-384b-discounted-repairs/) `batch_repair_saves` and `maxcut_repair_saves` bound the unrestricted 2-domination number. The lift used here needs the constructed set to retain its designated pins. The local theorem `trial_repair` returns that set, and `pair_frequency` proves the required sample count. The published 30-vertex sampler uses a 26-vertex pool and omits two cubics. This proof uses a 24-vertex pool and removes scores one and two or another specified low score. [Published sampler](https://github.com/vjdad4m/maths/blob/main/graffiti-384b-thirty-nonleaves/ThirtyPairSample31.lean)

## A forced five-vertex subgraph

In every failure the two closed neighborhoods of the ear neighbors together miss at least two vertices of degree at most nine whose triangle count exceeds the balanced bipartite bound `floor(deg²/4)`. They miss at least one such vertex of degree at most eight. The same conclusions hold for the closed neighborhood of any single specified vertex. The proof combines the uniform ten-vertex sample with a sample retaining the specified one or two vertices and nine others. It counts the rank-zero ear as already supported in the two-pin calculation. [Weighted tables](FourCharges28.lean) · [Theorem `remote_count`](FourLocal28.lean)

Through at least one of the remote centers there is a triangle joined to two nonadjacent vertices, an induced five-clique minus one edge. For the ear-neighbor application all five vertices lie outside `{e,p,q}`. In a link without two triangles sharing an edge, deleting a triangle costs at most one crossing edge per other vertex. Induction through link size nine proves the bipartite bound with a single exception for the three-vertex triangle. Distinct counts allow at most one such exceptional center, and the sampling theorem supplies two. [Extremal link proof](FourDiamond28.lean) · [Five-vertex construction](FourFan28.lean)

The three vertices of the central triangle give three possible vertices to omit from both sides of a pinned cut. Their other two triangle vertices and the two tips form its protected four-cycle. A cubic seeing all three triangle vertices can be pinned with the tips. For each fourth vertex on an ear square, every central vertex other than that fourth vertex therefore has an external cubic neighbor missing some member of the central triangle. With two choices of fourth vertex this forces both cubic scores outside the five-vertex configuration and the ear triangle. [Cut obstruction](FourWheel28.lean) · [Ear and cubic coverage](FourEar28.lean)

## Replay and remaining scope

With Lean v4.19.0, Mathlib v4.19.0 at `c44e0c8ee63ca166450922a373c7409c5d26b00b`, and the [diversity-29](../graffiti-384b-diversity29/) and [31-count](../graffiti-384b-thirty-nonleaves/) dependency objects on the Lean search path, build the 23 modules in `modules.txt` order with synchronous elaboration and warnings as errors. Check the exact source hashes with `sha256sum -c NEW-SOURCES.sha256`. Two recorded replays matched 266 predecessor objects, rebuilt the 14 extensions, and audited 26 standard-axiom reports. [Core transcript](StrictCore28.log) · [Ear-square transcript](StrictFour28.log).

The five-clique-free branch remains open when no fourth vertex exists and in square configurations satisfying the surviving score, degree, link and cubic restrictions. The five-clique and other nonleaf quotas are not fully resolved.
