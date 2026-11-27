# Graffiti.pc #384b with thirty triangle-count types

Every finite simple graph on n vertices with exactly 30 distinct vertex triangle-incidence counts has a 2-dominating set of size at most n − 15. This holds for disconnected graphs as well as connected graphs. A vertex’s triangle count is the number of unordered adjacent pairs among its neighbors. The set of counts includes zero when realized. Every vertex outside a 2-dominating set has at least two distinct neighbors in the set. [Catalogue inequality and existence theorem](DiversityThirty384b.lean)

The proof also establishes a general criterion. Write t for the number of triangle-count types and q for the number of vertices of degree at least two. Whenever t is even and q < t, the catalogue bound γ₂ ≤ n − ⌈t/2⌉ holds. [Even-diversity theorem](EvenNonleaves384b.lean)

## Proof

**Fewer nonleaves than types.** All vertices outside the nonleaves P have triangle count zero. Thus t ≤ 1 + |P|. If |P| < t, equality holds and the |P| nonleaves have distinct positive triangle counts. The induced graph H on P preserves each count. Every vertex of H lies on a triangle, so every vertex is a nonleaf in H. The checked one-ear theorem applies because score one occurs at most once, there are no zero-count vertices, and |P| equals the number of types in H. This gives at least ⌈(t−1)/2⌉ omissions. Every omitted vertex already has its two required neighbors in H, so the omissions work in G. For even t they give the full ⌈t/2⌉. At t = 30 this closes q = 29. [Count preservation and lifting](EvenNonleaves384b.lean) · [Published one-ear theorem](https://github.com/vjdad4m/maths/blob/main/graffiti-384b-one-ear/src/OneEarFinish384b.lean)

**At least 30 nonleaves.** Suppose t = 30 and the bound fails. Let h count the vertices of degree at least three. The established type bound t ≤ h + 2 and the maximum-cut omission bound ⌈h/2⌉ force h = 28. Thus at least two vertices have degree two. For each of the degrees 3, 4, 5, 6 realized by a vertex with a complete neighborhood, choose one such vertex. Let f record these degrees and let m = 28 − |f|. Keep an eleven-vertex sample from the other m high vertices. The published sampling lemma accounts for deficient unsampled vertices, degree-two omissions, and representatives whose neighborhoods contain two sampled vertices. A failure would impose a numerical inequality. The new strict inequality contradicts it for all 16 subsets f of the four tested degrees. Lean checks both the table and the connection between a graph and its table row. [Graph argument and finite table](SampleThirty384b.lean)

Together these two cases cover all nonleaf counts at every graph order. No induced-order cutoff, assumed failure at another diversity, or external graph enumeration is needed. The cases of #384b at other diversities retain their previous status. [Shared result index](https://github.com/vjdad4m/maths/blob/main/README.md)

## Source and replay map

| New module | Imports and checked results |
| --- | --- |
| EvenNonleaves384b | Imports OneEarFinish384b. Reuses Prune.counts_preserved, Prune.outside_zero, TrianglePrune.induced_cost, Capacity.seeded_value and OneEar.unique_one. Proves the general lifting rule and even-diversity criterion. |
| SampleThirty384b | Imports CliqueSample384b. Reuses type_bound, exact_of_high, CliqueChoice.choose_from and CliqueSample.obstruction. Proves the 16-row certificate and the result when q ≥ 30. |
| DiversityThirty384b | Imports those two modules. Proves exact_thirty_types and gives the explicit existential statement exists_set. |

The immediately preceding diversity-31 closure uses two forced cubics of triangle counts two and three. Its graph theorem assumes 31 types. The clique sampler and the earlier one-ear theorem have hypotheses the present graph satisfies directly, so this delivery depends only on the frozen one-ear release. The public one-ear replay builds the baseline from the pinned order-34 sources. [Public one-ear package](https://github.com/vjdad4m/maths/tree/main/graffiti-384b-one-ear)

## Strict replay

On Lean 4.19.0 with Mathlib v4.19.0, build the [one-ear package](../graffiti-384b-one-ear/) and its dependency closure first, retaining the resulting objects on the search path, including `OneEarFinish384b` and `CliqueSample384b`. Then compile these three modules in `modules.txt` order using synchronous elaboration with warnings as errors. The new files and their exact source digests are recorded in `NEW-SOURCES.sha256`. The strict replay log covers all six named theorems, with only standard axioms.
