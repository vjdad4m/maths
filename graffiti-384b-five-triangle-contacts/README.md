# Graffiti.pc #384b with two independent ears and five triangle contacts

Let `G` be a finite simple graph with 29 distinct vertex triangle counts, 29 vertices of degree at least two, and 27 vertices of degree at least three. Let `e,f` be its two degree-two vertices. In the remaining four-anchor case, their neighbor pairs `A = N(e)` and `B = N(f)` are disjoint subsets of the high vertices (degree at least three). The pool `X` consists of the 23 other high vertices. Write `T` for the number of vertices of `X` on a triangle with some vertex of `A∪B`. Write `M` for the number of vertices of `X` having any neighbor outside `X`, and `D` for the number having at least two such neighbors.

**If `T≤5`, the catalogue bound gives γ₂(G) ≤ |V(G)| − 15.** It also holds for arbitrary `T` if all four anchor triangle counts are at most 12. The graph-level results allow disconnected graphs, isolated vertices and leaves. In their formal statements, the published reductions recover disjoint high neighbors and distinct high triangle counts from a hypothetical failure. [Catalogue of Ermelinda DeLaViña](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/index.html) · [UHD conjecture records, entry 384b](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json) · [Global low-anchor theorem](LowPairAnchors.lean) · [Five-contact theorem and residual](FiveFront.lean)

A failure in this profile must have an anchor on at least thirteen triangles and satisfy **6 ≤ T ≤ M ≤ 14**, with D ≤ 6 if M = 14 and D ≤ 10 if M = 13. A further local test works at every `T`. Choose any five extra high vertices. If, inside the eleven vertices consisting of these five, the four anchors and the two ears, each anchor is on at least two triangles and one is on thirteen or more, the bound holds in the original graph. The theorem `protected_patch` only requires the indicated pattern, the nonleaf quota and coverage of all degree-two vertices. [Induced patch and exact hypotheses](FiveFront.lean)

## Low anchor counts

Pass to the graph induced by the 29 nonleaves. All triangle counts are preserved. With disjoint anchor pairs, average four kinds of twelve-vertex starting sets. The following multiplicities apply to each individual sample.

| Fixed vertices | Vertices sampled from the 23-vertex pool | Multiplicity |
|---|---:|---:|
| Both ears | 10 | 1 |
| `A` and ear `f` | 9 | 3 |
| `B` and ear `e` | 9 | 3 |
| `A∪B` | 8 | 5 |

Each omitted deficient vertex costs one repair. A selected vertex whose neighborhood is a clique and has at least two selected neighbors can earn one removal. The published simultaneous-removal proof and its counting lemma apply because the triangle counts in the pool are distinct. If the core requires at least fifteen vertices for two-domination, the total repair cost minus removals must be at least 25,496,328. A kernel-checked table indexed by the ranks of the 27 high triangle counts bounds the same total above by 29,199,990 − 4 × 935,272 = 25,458,902 when each anchor count is at most twelve. The strict margin is 37,426. The induced-core transfer yields the original graph inequality. [Sampling and simultaneous credit in the 30-nonleaf predecessor](https://github.com/vjdad4m/maths/tree/b33aad93ffcaab8f8c9e21a6fc56592675782f6f/graffiti-384b-30-nonleaf-complete) · [New rank table](PairRows.lean) · [New weighted estimate](PairSaving.lean)

## A protected cut on eleven vertices

Pad the at most five contacts to five vertices of the pool. Every triangle through an anchor lies in the resulting eleven labels, since a triangle vertex has degree at least two and the low vertices there are exactly the two ears. The four anchor scores are therefore their actual global scores. They are all at least two in a hypothetical failure. The averaging result covers the case that their maximum is at most twelve. [Embedding and triangle counts](FiveEmbed.lean) · [Original-graph reduction](FiveFrontData.lean)

For a larger maximum, relabel the two ear pairs to make label zero the distinguished anchor. Among the nine high labels there are 36 optional edges. A binary tree splits on the presence of individual edges. A triangle-count leaf computes an upper bound with every unresolved edge present. A cut leaf provides two explicit disjoint sets with both ears pinned and each pinned vertex already having two neighbors pinned on the opposite side, even with every unresolved edge absent. Both tests are monotone under the indicated edge bounds. The certificate has 1,818 binary splits, 1,197 cut leaves and 622 triangle-count leaves. Ordinary Lean kernel reduction checks every leaf. The graph-level proof then invokes the predecessor’s pinned maximum-cut theorem. This cut argument allows repeated triangle counts at the other anchors. [Checker and soundness](LocalTree.lean) · [Ear-pair relabeling](FiveSym.lean) · [Root certificate](Case0Cover.lean) · [Transfer of a protected cut](FiveEmbed.lean)

The four-contact predecessor (source archive SHA-256 `22e5e701d1e366e2b24c1490ab880d18ebb1b558bd3eb8c763c70ba521aac9f9`) supplies the definition of triangle contacts, the strict profile reductions and the upper bounds on exposure. Its previously certified five-contact configuration can obstruct a cut confined to the patch when the anchor counts are small. The new sampling theorem covers that case. The 30-nonleaf result supplied the simultaneous credit; its three-ear arithmetic and profile theorem are specific to a different nonleaf profile. The new proof uses the two-ear arithmetic above.

## Replay

The source archive includes all project imports, eight finite data files, manifests and the strict replay script. Lean is pinned to 4.19.0 commit `6caaee842e94`, and Mathlib to `c44e0c8ee63ca166450922a373c7409c5d26b00b`. In the shared workspace, run this from the proof directory:

```sh
python3 -B replay.py --checked ..
```

In an extracted source package, set the toolchain and initialized Mathlib checkout explicitly. The optional checked mode takes the original workspace as its argument. A fresh machine can build the complete transitive source closure:

```sh
FIVE_LEAN_BIN=/absolute/path/to/lean-4.19.0-linux/bin \
FIVE_MATHLIB=/absolute/path/to/mathlib4-4.19.0 \
python3 -B replay.py --cold
```

The extracted-package replay verified 20 new modules and 30 axiom reports against 329 hash-matched predecessor objects. A second extraction rechecked both terminal modules. The predecessor sources are included for a cold build. [Strict replay transcript](StrictFive.log) · [Terminal cross-check](PackedTerminals.log)

Every newly compiled module uses synchronous elaboration and warnings as errors. The driver verifies the exact source closure, checks printed theorem axioms against `propext`, `Classical.choice` and `Quot.sound`, and rejects unproved placeholders and native evaluation shortcuts.

[Complete pinned Lean sources](proof-sources.zip). Extract the archive and use its replay script.
