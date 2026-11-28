# Graffiti.pc #384b for a leaf attached to a rich vertex

Let `t` count the distinct numbers of triangles incident to a vertex and let `q` count the vertices of degree at least two. Ermelinda DeLaViña's January 2010 catalogue asks whether a connected graph of order `n>2` has a two-dominating set of size at most `n−⌈t/2⌉`. Each vertex outside the set needs two distinct neighbors in it. The results here address rich leaf attachments in the minimum case `q=t−1`. Their conclusions also apply at other quotas because every finite simple graph has `t≤q+1`. [Official catalogue](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/index.html) · [Catalogue entries](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json)

## Two graph-level sufficient conditions

* **Articulation at the leaf's neighbor.** Delete the nonleaf `r` adjacent to the leaf from the graph induced by all nonleaves. Suppose this disconnects that core, every remaining vertex lies in a triangle inside its remaining subgraph, and each component of the graph formed by its triangle edges has at most one vertex lying in exactly one such triangle. Then the original connected graph satisfies #384b. All triangle counts in this test are recomputed after deletion. [ArticulationRoot.lean](ArticulationRoot.lean)
* **A leaf next to an ear anchor.** Write `z–r–e–b` for the path from the leaf, where `r,e,b` are distinct nonleaves. The triangle `reb` is the intended ear configuration. Set `S` equal to the other nonleaves. If every vertex of `S` has original degree at least five and `b` is adjacent to strictly more than `⌈|S|/2⌉` vertices of `S`, the graph satisfies #384b. This conclusion uses only the three path edges and permits additional edges. With the same contact inequality, any failure requires an exterior vertex of degree at most four. The precise obstruction is `degree(v)+neighbors(v,K) < 3+neighbors(v,{r,b})`, where `K` consists of the always-retained vertices outside `S∪{r,b}`. A strict local majority of neighbors inside the contact set can replace the contact inequality. [LocalFrontier.lean](LocalFrontier.lean) · [DegreeExchange.lean](DegreeExchange.lean)

These are sufficient conditions. In particular, the general minimum-quota case with a rich leaf neighbor remains open in this package.

## Why the leaf supplies an extra omission

For the articulation argument take `S` to be the nonleaves other than `r`. The leaf is always retained and supplies one neighbor if `r` is omitted. The published rich-core cut protects all rich vertices and any one vertex of score one. Apply its cut separately within each component of the residual triangle-edge graph, selecting that component's vertex of score one if present. This yields two shores of `S`, each vertex having at least two neighbors across. [ResidualCut.lean](ResidualCut.lean)

If `r` has a contact on both shores, either shore can be omitted together with `r`. If the catalogue inequality fails, all contacts must lie on the larger shore and its size exceeds the other by exactly one. Reversing both colors in a region that has no triangle edge leaving it preserves coverage. Hence any such region with an outside contact must contain no contacts and must have equally many vertices on the two shores. An articulation of the original nonleaf core puts a contact in each of at least two distinct residual components. Reversing one separates two contacts, proving the result. The protected-cut obstruction also excludes a contact having at most one residual triangle-edge neighbor outside the contact set. [ContactShore.lean](ContactShore.lean) · [ComponentExchange.lean](ComponentExchange.lean)

For the path argument keep `z,e` in both trials and always omit `r`, which sees both. The other pivot `b` sees the retained `e` and needs only one retained contact. Keeping the vertices of `K` in both trials lets their incident edges count twice in the maximum-cut degree estimate. The general exchange theorem accepts either the residual triangle conditions and a contact test, or this degree estimate and a density test. [RichLeafRoot.lean](RichLeafRoot.lean)

## Tests on original graphs

A connected 13-vertex graph has 12 nonleaves, 13 distinct scores and a leaf at a vertex of score 28. That root is adjacent to a score-one ear. The ear's other anchor meets seven of the other nine nonleaves. Lean verifies the profile and the catalogue inequality via the exchange theorem. A second connected example applies the local contact test away from the ear. [RichRootExamples.lean](RichRootExamples.lean)

The tight contact pattern alone can occur at equality. Move the leaf in the published nine-vertex example to vertex 2 of its core. The new root has score three. Its contacts all lie in a protected four-vertex shore opposite a three-vertex shore. The graph still has `γ₂=4=n−⌈t/2⌉`. Lean checks a set of size four and rules out every smaller set. This example limits the converse of the cut obstruction. [Formal certificate](RichRootExamples.lean) · [Original nine-vertex construction](https://github.com/vjdad4m/maths/blob/b8a9f5c81297889a345be81df6e702c9b46b3338/graffiti-384b-leaf-cuts/PairExample.lean)

## Source and replay

The proof reuses the published `cover_rich_ear`, `covers_high`, `Prune.connected_core`, and `Repair.asymmetric_cut`. It extends the earlier leaf-at-score-one proof's two-trial counting by fixing a different omission and allowing contacts to be separated across components. The earlier `prescribed_edge` requires appropriate triangle scores at two specified endpoints. Here a cut of the residual vertices and the single retained leaf suffice. The two published source closures also contain overlapping declarations under different module names, so this package imports the rich-core release and reproduces the small quota bound directly. [Rich-core release at 8b6a808](https://github.com/vjdad4m/maths/tree/8b6a808f3dfe98d850051ec4a422520a19b16952/graffiti-384b-ear-exchange) · [Prior rooted theorem at b8a9f5c](https://github.com/vjdad4m/maths/tree/b8a9f5c81297889a345be81df6e702c9b46b3338/graffiti-384b-minimum-quota-ear-root) · [Shared index checked](https://github.com/vjdad4m/maths/blob/f32f1fa3a96ffe06e487413b02a3c6cf01b622d3/README.md)

The package contains eight new Lean modules, their 80 transitive project dependencies, source hashes, object hashes and a strict transcript. The source SHA-256 of the upstream ear-exchange archive is `66f5ad3c03905c624b6a5e7675bc42c4319d389d30e825ec21d0d7c396a33deb`. Lean 4.19.0 is pinned at `6caaee842e94` and Mathlib at `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The runner checks every project source hash, rebuilds serially with warnings as errors, and checks every new printed axiom report against `propext`, `Classical.choice` and `Quot.sound`. [Replay script](replay.py) · [Transcript](StrictRichRoot.log)

From the extracted directory in the shared workspace run

```bash
ws=/workspace/scratch/7efa613b1c05
export RICHROOT_LEAN_BIN="$ws/graff384b-codex/.deps/lean-4.19.0-linux/bin"
export RICHROOT_MATHLIB="$ws/graff384b-codex/.deps/mathlib4"
python3 -B replay.py --checked "$ws"
```

The recorded run authenticates the 80 predecessor objects against the published archive and recompiles the eight new modules from the extracted source. A workspace without these objects can set the same two variables to compatible installations and run `python3 -B replay.py --cold` to rebuild every project module.

[Complete pinned Lean sources](proof-sources.zip). Extract the archive and use its replay script.
