# Connected planar chordal graphs with sub-total domination two and unbounded power domination

For each integer k ≥ 2, there is a connected planar chordal graph on 4k+2 vertices with sub-total domination number 2 and power domination number k+1. Thus even on the intersection of these classes, no function of the sub-total domination number alone bounds the power domination number. The first member has 10 vertices and gives 3 versus 2. [Graph and degrees](Book.lean) · [Power domination](Forts.lean) · [Plane drawings](PlanarFamily.lean)

## Catalogue claims

| Pinned physical row | CEGIS ID | Domain | Claim |
|---|---|---|---|
| [567](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L567) | `b2d82b19` | Nontrivial connected chordal graphs | Power domination ≤ sub-total domination |
| [383](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L383) | `69107966` | Nontrivial connected planar graphs | Power domination ≤ sub-total domination |

Both records have status `proposed` and no attached Lean proof at revision `4d1a8afc99447cacd2328cca20e47b6493e8dbc5`. Their normalized touch counts are 164 and 252 respectively. These are the two occurrences of this consequent in the normalized file. The shared index at `d41a87d860a47a69914fc567370f5ed1b4d06fb7` contained neither row. The public upstream issue concerns a different record. [CEGIS records](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/cegis_results.json) · [Shared index](https://github.com/vjdad4m/maths/blob/d41a87d860a47a69914fc567370f5ed1b4d06fb7/README.md) · [Issue 1](https://github.com/JanPastorek/AutoGraphForge/issues/1)

## Construction and proof

Take two adjacent hubs and add 2k page vertices adjacent to both. Attach two private leaves to each of k pages, called the supports. The other k pages are plain. Both hubs have degree 2k+1, giving a two-term degree sum equal to the order. In a finite nontrivial simple graph one degree is always smaller than the order. Consequently the first degree prefix whose sum reaches the order has length two. The lemma `subTotal_two_of_pair` works for any finite simple graph with a pair of distinct vertices whose degrees sum to at least its order.

Two distinct vertices with identical open neighborhoods cannot first be observed by ordinary forcing while both remain unobserved. At least one must therefore lie in the initial closed neighborhood of a power-dominating set. Each support and its two leaves form one required seed region. Two plain pages give a further required region contained in the plain pages and hubs. All k+1 regions are disjoint. Taking the k supports and a hub observes the entire graph in the initial domination step. This proves the minimum exactly.

Every vertex reaches a hub. Eliminate the leaves first, then the pages, then the hubs to certify chordality. For planarity put the hubs at ((-1,0)) and ((1,0)). In block i, put the plain page, first leaf, support and second leaf at four consecutive positive integer heights on the vertical axis, beginning at 4i+1. Draw straight edges. On either side of the vertical axis, the horizontal coordinate fixes the interpolation parameter of a spoke and the vertical coordinate then fixes its endpoint. Vertical leaf edges join consecutive integer levels. Lean checks that every arc embeds, reversing an edge reverses its arc, every open edge avoids every vertex, and distinct open edges are disjoint. The certificate works for all k.

## Implementation, attribution and earlier witnesses

GraphCalc 2.0.0 sorts the degree sequence in decreasing order and searches the prefix lengths from 0 through the order. The Lean function `subTotal?` has type `Option ℕ` and its exact value here is `some 2`. GraphCalc starts power domination with the closed neighborhood of the seeds and applies the ordinary one-unobserved-neighbor forcing rule. The Lean inductive closure uses the same initial and propagation rules. Nontriviality means order at least two. Chordality forbids induced cycles of length at least four. GraphCalc recognizes planarity with NetworkX, and the Lean artifact supplies an actual plane embedding by segments. [Degree code](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/invariants/degree.py#L376-L437) · [Power domination code](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/invariants/zero_forcing.py#L1059-L1304) · [Graph predicates](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/core/basics.py) · [Invariant battery](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/pipeline/invariants_graphcalc.py)

The twin-pair argument is a special case of the established characterization of power domination by hitting closed neighborhoods of zero-forcing forts. Dávila introduced the sub-total degree invariant. Searches for their joint inequality on planar and chordal graphs located no publication giving the fixed-value family above. Priority for this family remains unestablished. [Smith and Hicks, *Networks*](https://doi.org/10.1002/net.22056) · [Dávila, *A note on sub-total domination in graphs*](https://arxiv.org/abs/1701.07811)

**The upstream release already contains a counterexample to both rows.** Its 32-vertex tree occurs under the two unrelated record IDs `b56729d4` and `88925c95`, each credited upstream to “cross-shard merge.” It has sub-total domination number 8 and ten disjoint pendant-leaf-pair neighborhoods. Their ten supports power-dominate. This establishes power domination number 10. The accompanying audit classified all 4,776 distinct released graph6 encodings from the backup corpus and the refutation files. This tree was the only failing encoding among 2,273 qualifying planar and 1,596 qualifying chordal encodings. The pinned battery also returned the predicted exact values on our 10- and 14-vertex graphs. The result supplied here is a strict proof of the unbounded gap at the smallest possible numerical sub-total value. [Earlier tree encoding and credits](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/cegis_refuted.json#L4139-L4152) · [Audit source](audit.py) · [Audit output](SourceAudit.log)

Four files package existing public Lean ingredients with their proofs. `PowerBasis` retains the inductive observation and power optimum of row 66. `ChordalBasis` uses row 1915’s elimination certificate. `DegreeBasis` adapts the sorted degree leaders from row 143 and the optional optimizer from row 362. `PlaneBasis` adapts the real-plane drawing predicate, segment interpolation and integer-level lemmas from row 464. The graph construction, exact optima, twin-pair lemma and parametric drawing appear in `Book`, `Forts` and `PlanarFamily`. [Row 66](https://github.com/vjdad4m/maths/blob/d41a87d860a47a69914fc567370f5ed1b4d06fb7/autographforge-66/PowerBurning.lean) · [Row 1915](https://github.com/vjdad4m/maths/blob/d41a87d860a47a69914fc567370f5ed1b4d06fb7/autographforge-1915/TriangleChain.lean) · [Row 143](https://github.com/vjdad4m/maths/blob/d41a87d860a47a69914fc567370f5ed1b4d06fb7/autographforge-cograph/CographRadius.lean) · [Row 362](https://github.com/vjdad4m/maths/blob/d41a87d860a47a69914fc567370f5ed1b4d06fb7/autographforge-362/BicliqueTail.lean) · [Row 464](https://github.com/vjdad4m/maths/blob/d41a87d860a47a69914fc567370f5ed1b4d06fb7/autographforge-464/Drawing.lean)

## Reproduction

With Lean 4.19.0 on PATH and Mathlib 4.19.0 built at `c44e0c8ee63ca166450922a373c7409c5d26b00b`, run from this directory.

```bash
MATHLIB_DIR=/absolute/path/to/mathlib4 bash replay.sh
```

The default replays all seven modules in a fresh object directory with warnings as errors and checks the six named axiom lists. `bash replay.sh 567` checks the chordal result alone. `bash replay.sh 383` adds the planar proof. All six printed axiom sets contain only `propext`, `Classical.choice` and `Quot.sound`. [Expected Lean output](Replay.log)

To repeat the independent numerical and source audit, use GraphCalc 2.0.0, NetworkX 3.5 and the pinned AutoGraphForge checkout with its pipeline dependencies.

```bash
python audit.py /absolute/path/to/AutoGraphForge
```
