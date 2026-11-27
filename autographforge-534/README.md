# AutoGraphForge row 534 — restrained and independent domination

**Row 534 holds.** For every finite simple Eulerian cograph of order at least two, the restrained domination number γᵣ is at most the independent domination number i. Pastorek's physical normalized row has 182 touches, the label `promising:class`, and generated ID `38975fcb`. The CEGIS record has status `proposed`, 2,062 raw touches, and empty Lean fields. Row 518 uses chordality and has a different domain. [Pinned row 534](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L534) · [Generated records](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/cegis_results.json)

## Exact criteria

Let G be a join of two nonempty finite simple graphs. The two factors can have arbitrary internal edges.

* **When the inequality holds.** γᵣ(G) ≤ i(G) if and only if every vertex has degree at least two.
* **When equality holds.** Under that degree condition, γᵣ(G) = i(G) if and only if the complement of G has an isolated vertex or has an edge that belongs to no triangle.
* **Why these conditions are sharp.** On the star with n leaves, γᵣ = n + 1 and i = 1. Within the Eulerian cographs, K₃ gives equality at 1, C₄ gives equality at 2, and K₄,₄ gives strict inequality 2 < 4. The star identities hold in Lean for every n. The three Eulerian examples are also evaluated by the upstream battery.

For a universal vertex u, let L be the vertices isolated by deleting u. Each vertex of L must be in every restrained dominating set, since its sole neighbor cannot lie both inside and outside the set. The set L alone fails. Its omitted center would need an outside neighbor, which in turn could have no neighbor in L. Adding u suffices, giving γᵣ = 1 + |L| and i = 1. This formula holds for every finite simple graph with a universal vertex.

If neither join factor supplies a universal vertex, each factor has at least two vertices. Choosing one vertex in each factor dominates the graph and leaves each unchosen vertex adjacent to another unchosen vertex in the opposite part. Thus γᵣ = 2. Every independent dominating set has size at least two. An independent dominating pair in G is precisely an edge in its complement whose ends have no common neighbor, which gives the equality test.

Seinsche's characterization makes every connected cograph of order at least two a proper join. A nontrivial connected Eulerian graph has positive even degrees, which establishes the catalogue hypotheses. [Seinsche (1974)](https://doi.org/10.1016/0095-8956(74)90063-X)

## Prior work and scope

Pandey and Panda studied restrained domination on cographs using cotree decomposition. The two-sided join case of Theorem 7.3 contains the two-vertex construction above. Their arXiv v1 singleton-join formula evaluates to n on the join of K₁ with an edgeless graph of order n ≥ 2. Both the number of isolated vertices and the ordinary domination number of the edgeless factor equal n. The restrained optimum is n + 1, already witnessed by P₃. The theorem `singleton_join_discrepancy` verifies this specific comparison. Chen and Sohn's 2021 paper expressly credits and corrects an earlier error and gives a linear-time algorithm for cographs. Its publisher preview exposed the abstract, so the comparison with a numbered formula here is confined to Pandey and Panda's public v1 text. The catalogue application and complement equality test are recorded as structural consequences. Historical priority for either is unestablished. [Pandey and Panda, Theorem 7.3](https://arxiv.org/pdf/1606.02340v1#page=16) · [Chen and Sohn (2021)](https://doi.org/10.1007/978-3-030-93176-6_36)

The shared index at `2fffcd667fe16d023f1a33ed02f14c9e09aa9fec` contained no row 534. The upstream pinned proof directory, the three refutation files, and the public issue list supplied no matching entry. The single public issue concerns ID `f0a6258d`. These checks identify the catalogue status and local contribution. [Shared research index](https://github.com/vjdad4m/maths/blob/2fffcd667fe16d023f1a33ed02f14c9e09aa9fec/README.md) · [Upstream results](https://github.com/JanPastorek/AutoGraphForge/tree/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results) · [Upstream issue](https://github.com/JanPastorek/AutoGraphForge/issues/1)

## Conventions and reuse

GraphCalc minimizes the number of selected vertices subject to closed-neighborhood domination. Its restrained optimizer requires each unselected vertex to have an unselected neighbor. Its independent optimizer forbids both endpoints of an edge from being selected. Eulerianity calls NetworkX on an undirected graph and requires connectivity and even degrees. Nontriviality means order at least two. Cographs are induced-P₄-free. These conventions give finite numeric values on the whole row domain. [Restrained optimizer](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/invariants/domination.py#L1341-L1410) · [Independent optimizer](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/invariants/domination.py#L313-L397) · [Eulerianity](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/core/basics.py#L552-L575) · [Cograph recognition](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/core/basics.py#L1126-L1194)

`Proof137.lean` is the checked structural excerpt packaged with row 143. `CographJoin.lean` extracts its induced-path definition, universal vertex and `join_at` theorem from that row. The source of row 143 separately proves equivalence with GraphCalc's recursive cograph test. `IndependentBasis.lean` extracts the `Dominates` predicate from the row 1078 dependency and the independent domination definition and attainment proof from row 2527, under the local namespace. The four source files used for extraction were byte-compared with the pinned public copies. The positive-even-degree argument adapts the existing row 1900 proof. [Row 143](https://github.com/vjdad4m/maths/tree/2fffcd667fe16d023f1a33ed02f14c9e09aa9fec/autographforge-cograph) · [Row 2527 and dependencies](https://github.com/vjdad4m/maths/tree/2fffcd667fe16d023f1a33ed02f14c9e09aa9fec/autographforge-2527)

## Replay

With Lean 4.19.0 on PATH and compiled Mathlib 4.19.0 at commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`, run from the extracted source directory.

```bash
MATHLIB_DIR=/absolute/path/to/mathlib4 bash replay.sh
```

The script strictly compiles seven source modules in a fresh temporary directory, with warnings as errors, and verifies the printed axiom sets of ten named results. The only axioms are `propext`, `Classical.choice`, and `Quot.sound`. For the optional numerical audit, use GraphCalc 2.0.0, NetworkX 3.5 and the pinned AutoGraphForge checkout with its pipeline dependencies.

```bash
python audit.py /absolute/path/to/AutoGraphForge
```

The audit screened 4,776 distinct released graph6 encodings. There were 691 connected nontrivial cographs, 229 in the row domain, including 14 in upstream refutations of other statements. Both optimizers and the structural formulas were checked on all 445 connected nontrivial cographs of order at most ten in the corpus. The upstream `compute_battery` also reproduced the P₃, K₃, C₄ and K₄,₄ examples. [Release audit output](SourceAudit.log) · [Strict Lean replay](Replay.log)

