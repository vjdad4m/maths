# Graffiti.pc #384b with 29 triangle-count types

Let `t` count the distinct numbers of triangles incident to individual vertices. Zero is included whenever it occurs. A 2-dominating set gives each vertex outside the set at least two distinct neighbors in the set. Write `q` for the number of vertices of degree at least two and `h` for the number of vertices of degree at least three. At `t = 29` the catalogue asks whether a graph of order `n` has a 2-dominating set of size at most `n − 15`. [Shared checked-result index](https://github.com/vjdad4m/maths/blob/main/README.md)

## The result

**Every finite simple graph with 29 types and at least 31 nonleaves satisfies the catalogue bound.** This covers disconnected graphs as well. The previously available `Lower.exact_of_quota` covered connected graphs at this diversity from 33 nonleaves. At every order and nonleaf count, the bound also holds when every vertex belongs to a triangle. For a hypothetical failure with 30 nonleaves the proof exhibits a vertex of degree four through eight whose triangle count exceeds the number of edges in the balanced complete tripartite graph on its degree. This same vertex belongs to a five-clique. In particular every five-clique-free graph with 30 nonleaves satisfies the bound. [Nonleaf theorem](QuotaFinish29.lean) · [Local threshold](QuotaLocal29.lean) · [Conclusions](FrontierTwentyNine384b.lean)

Any failure has zero among its counts, has 27 or 28 vertices of degree at least three, and has 28, 29 or 30 nonleaves. Every connected failure contains a connected induced failure of order 29, 30 or 31 with exactly the original set of counts. The upper bound 31 applies to this induced graph. The restriction on the original graph is on its number of nonleaves. At 28 high vertices every degree-two vertex has two high neighbors, and the union of the high neighborhoods of any family of degree-two vertices has twice as many members as the family. [Residual, induced and disjoint-anchor theorems](FrontierTwentyNine384b.lean)

## How the high-count estimate works

1. Under a failure, applying the existing independent-omission bound to a set of nonadjacent degree-two vertices forces a lower bound on the number of their distinct high neighbors. Deleting at most one degree-two vertex makes the entire family independent. With at least 31 nonleaves this supplies five distinct high vertices for `h = 27` or four for `h = 28`. Each has a neighbor fixed outside the sampling pool. [Exposure argument](ExposedQuota29.lean)
2. Choose one representative of each tested degree from three through nine realized by a vertex whose neighbors form a clique. Sample the remaining high vertices. A fixed neighbor lowers the number of samples in which its high neighbor has insufficient support. The proof incorporates that saving into the double count of bad samples. Lean checks the degree-rank inequalities for both possible high counts and all 128 subsets of tested degrees. The proof forces a center of degree six, seven or eight with at most its degree minus five missing edges among its neighbors. The chosen representatives have degree at most four. [Sample count](QuotaFiber29.lean) · [Dense neighborhood](QuotaDense29.lean)
3. Fix that center and account for all its neighbors simultaneously. Their degrees are at least five, so none is a chosen representative. The earlier block count and the fixed-neighbor savings then contradict the assumed failure to omit fifteen vertices. The finite calculations are in the Lean kernel. [Final counting inequality](QuotaFinish29.lean)

## What replaces the even-diversity lifting argument

For any graph let `P` be its nonleaves. Every degree-zero or degree-one vertex belongs to every 2-dominating set. The maximum feasible omissions from `P`, counting these forced vertices as available neighbors, plus the 2-domination number equals the graph order. At odd diversity `t` with `q < t`, one has `q = t − 1`. A failure occurs exactly when the rooted maximum number of omissions equals `q/2`. In a failure, the induced graph on `P` has distinct positive triangle counts and 2-domination number exactly `q/2`. [Rooted equivalence](OddQuota384b.lean)

Call a subset of the core *triangle-closed* if no triangle meets both it and its complement. Edges that belong to no triangle may cross. If a triangle-closed subset has odd size, applying the half-order bound separately on the two trimmed sides supplies the additional omission. Thus at 29 types and 28 nonleaves, a hypothetical failure requires a 28-vertex core of 2-domination number 14, in which every triangle-closed subset has even size. The rooted equivalence and the odd-subset test apply at every odd diversity with fewer nonleaves than types. Whether these obstructions can all occur in a 29-type counterexample remains open. [Parity theorem](OddShore384b.lean) · [Specialization to 28 nonleaves](FrontierTwentyNine384b.lean)

## Reuse and source map

| New module | Frozen results used and contribution |
| --- | --- |
| ExposedQuota29 | Uses `Repair.exact_of_low_support` and `CliqueChoice.neighbors_in_pool` to count distinct fixed-neighbor savings. |
| QuotaFiber29 | Adapts the earlier unified sampling obstruction to a degree-nine bound with a vertex-dependent saving, using `BlockLoss.pool_loss`. |
| QuotaDense29 | Uses the new sample count and `CliqueChoice.profile` to force a dense neighborhood. |
| QuotaFinish29 | Adapts the block-center strategy from `Finish31Boundary384b`, using `VariableBlock.balance` and `BoundaryFiber.count`. Its numerical rows and the 29-type hypotheses are checked afresh. |
| QuotaLocal29 | Uses `UnifiedSample.extraObstruction` and the tripartite degree cap to cover 30 nonleaves under local constraints. |
| OddQuota384b | Uses `OneEar.unique_one`, `Prune.counts_preserved`, `TrianglePrune.induced_cost` and the `Capacity` API to characterize odd-diversity failure at the minimum number of nonleaves. |
| OddShore384b | Uses `OneEar.trim`, `TrianglePrune.scores_closed` and `Capacity.separated_add` to combine the two triangle-closed sides. |
| IsolateBasic384b | Reuses the general isolated-vertex construction, palette and domination proofs from the frozen local `graff384b-isolate31/IsolatedVertex31.lean` (SHA-256 `10db10df370530f7798493419ea3317a930f32689500b6ec10d1936e4e647548`). This extract has a distinct namespace and imports the baseline graph definitions. |
| FrontierTwentyNine384b | Uses the complete frozen 30-type theorem after adjoining an isolate when zero is missing, and `Prune.prune_failure` for the induced reduction. Localizes the proof of `RankTuran.local_turan` to put a five-clique through the actual vertex exceeding the density cap. |

The frozen 30-type theorem supplies exactly the positive-count case here, since adjoining one isolate increases both the order and the number of types by one. The specialized 31-type distinct-anchor conclusions have a different diversity hypothesis. The published one-ear theorem supplies the half-order bound on a core of pairwise distinct positive counts. [Published one-ear source](https://github.com/vjdad4m/maths/blob/main/graffiti-384b-one-ear/src/OneEarFinish384b.lean)

## Strict replay

Use Lean 4.19.0 with pinned Mathlib v4.19.0. Build the [diversity-30 package](../graffiti-384b-diversity30/) and its [one-ear](../graffiti-384b-one-ear/) and pinned order-34 dependencies, retaining their objects on the Lean search path. Compile the nine new modules in `modules.txt` order with synchronous elaboration and warnings as errors. Source checksums and the complete strict audit are included; the full 29-type case and the general conjecture remain open.
