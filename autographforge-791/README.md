# AutoGraphForge 791. A cubic counterexample for singleton three-rainbow domination

**A connected simple cubic graph on 20 vertices has singleton three-rainbow domination number 13 and minimum maximal matching number 6.** Ján Pastorek’s normalized physical row 791 asserts that every cubic graph of order at least two satisfies `three_rainbow_domination_number ≤ 2 · min_maximal_matching_number`. The witness requires 13 ≤ 12. Both optima, connectivity, cubicity, and the negation of the row are kernel-checked. [Pinned row 791](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L791)

GraphCalc 2.0.0 assigns each vertex either zero or exactly one of three colors. Every zero must have a neighbor of each color, and the cost is the number of colored vertices. Its matching wrapper minimizes domination on the line graph. Lean checks this optimizer and also the minimum cardinality of a maximal matching defined directly by disjoint edges. The latter equality with edge domination in general is classical. [GraphCalc rainbow program](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/invariants/domination.py#L1153-L1185) · [Matching wrapper](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/invariants/domination.py#L1464-L1490) · [Yannakakis and Gavril, *Edge Dominating Sets in Graphs*](https://doi.org/10.1137/0138030)

## Construction

Start with eight independent vertices, called sites, labeled 0 through 7. Each additional vertex is adjacent to the two indicated sites. Join the two additional vertices in each table row. These 30 edges specify the entire graph.

| Added vertex | Its two sites | Matched partner | Partner’s two sites |
|---:|---|---:|---|
| 8 | 0, 1 | 9 | 0, 2 |
| 10 | 1, 2 | 11 | 1, 2 |
| 12 | 3, 4 | 13 | 3, 5 |
| 14 | 4, 6 | 15 | 4, 7 |
| 16 | 5, 6 | 17 | 5, 7 |
| 18 | 0, 3 | 19 | 6, 7 |

The six partner edges form a maximal matching and dominate every edge. They also form an induced matching, so any graph edge can meet at most one partner edge. Every edge-dominating set therefore has size at least six.

## Why twelve colored vertices cannot suffice

In a cubic graph, an uncolored vertex must see all three colors on its three neighbors. Its neighbors are colored and pairwise different in color. Thus the uncolored vertices form an independent set. For this graph the eight sites are the only independent set of size at least eight.

To see the uniqueness, split the sites into the left side {0,1,2} and the right side {3,4,5,6,7}. Consider any independent set Z. For each selected additional vertex other than 18, both incident sites are excluded from Z. Assign that vertex to the smaller of its two sites. On each side this assignment is injective. Vertices with the same smaller site are matched partners, and Z can take at most one. Moreover, whenever any site on a side is excluded, the greatest excluded site on that side is unavailable as an assignment: every assigned site has a greater excluded neighbor in the same pair of sites. If 18 is selected, it excludes one site on each side, leaving at least two unassigned excluded sites to account for it. Otherwise a selected additional vertex already leaves one extra site excluded. In either case selecting any additional vertex gives |Z| ≤ 7.

A labeling of weight at most 12 would leave all eight sites uncolored. Sites 1 and 2 then see the same colors on their common neighbors 10 and 11, forcing the same third color on 8 and 9. Site 0 sees 8, 9, and 18, and requires three different colors. This contradiction proves the lower bound. The following coloring attains 13.

| Color | Vertices |
|---|---|
| 1 | 0, 10, 14, 17 |
| 2 | 8, 9, 12, 13, 19 |
| 3 | 3, 11, 15, 16 |

All unlisted vertices are uncolored. Žerovnik studies the singleton convention for cylindrical graphs. The upper and lower bounds here concern the specific graph above. Targeted searches located no earlier explicit resolution of this exact catalogue row. The smallest counterexample order and historical priority are unverified. [Žerovnik, *On Singleton 3-Rainbow Domination of Cylindrical Graphs*](https://doi.org/10.3390/math14162917)

## Catalogue and public-repository audit

At pin `4d1a8afc99447cacd2328cca20e47b6493e8dbc5`, the canonical CEGIS record is `5550b3d6`, with status `proposed` and empty Lean fields. The normalized file gives 97 touches, while the CEGIS metadata gives 630. Physical line 2732 (`81cb4a70`) gives the algebraic half-ratio and 2733 points back to 791. Lines 3754 (`27dd6555`) and 5177 (`8fc5440b`) give the strict antecedents and conclude noncubicity. They omit the order hypothesis. The same order-20 graph falsifies all forms; the Lean theorem `other_spellings` checks their numerical conditions. We count one mathematical result. Row 1883 compares the same two parameters in the opposite direction under different hypotheses. The 5169 and 5170/5174 certificates compare matching with edge cover. [Explicit alias](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L2732-L2733) · [First strict antecedent](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L3754) · [Second strict antecedent](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L5177)

All four IDs were absent from the three refutation JSON files, the released verified Lean files, and the inspected public maths index at `f128a6b93df260f69810a66c05ba94fcba92be68`. The sole upstream issue concerned a different ID. The 4,776 distinct released graph6 encodings include 118 eligible cubic inputs. All satisfied the inequality. For 110 inputs the audit verified an explicit labeling against the componentwise bound that each selected edge dominates at most five edges. Five more used a verified labeling and GraphCalc’s matching optimizer, and three used both optimizers. The upstream public `compute_battery` entry point returned 13 and 6 on the new witness. The graph6 encoding and counts are saved in `SourceAudit.log`. [Release data](https://github.com/JanPastorek/AutoGraphForge/tree/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results) · [Inspected public index](https://github.com/vjdad4m/maths/blob/f128a6b93df260f69810a66c05ba94fcba92be68/README.md) · [Upstream issue](https://github.com/JanPastorek/AutoGraphForge/issues/1)

## Sources and replay

`Graph.lean` gives the graph and exact matching optima. `Independent.lean` proves the independent-set uniqueness lemma, and `Row791.lean` proves the exact rainbow optimum and disproof. The singleton labeling interface, matching model and line domination definition are the published rows 1121 and 1078 modules, matched byte for byte. `Packing.lean` uses the published row 659 induced-matching lemma verbatim. All project imports are included. [Singleton labeling](https://github.com/vjdad4m/maths/blob/f128a6b93df260f69810a66c05ba94fcba92be68/autographforge-1121/HallRainbow.lean) · [Matching model](https://github.com/vjdad4m/maths/blob/f128a6b93df260f69810a66c05ba94fcba92be68/autographforge-1078/Row1078.lean) · [Induced-matching packing](https://github.com/vjdad4m/maths/blob/f128a6b93df260f69810a66c05ba94fcba92be68/autographforge-659/Theta.lean)

With Lean 4.19.0 on PATH and a built Mathlib 4.19.0 checkout at `c44e0c8ee63ca166450922a373c7409c5d26b00b`, run

```bash
MATHLIB_DIR=/absolute/path/to/mathlib4 bash replay.sh
```

The replay compiles all eight sources in a fresh directory with warnings as errors and verifies that each of seven main theorems depends only on `propext`, `Classical.choice` and `Quot.sound`. The expected output is in `Replay.log`. With GraphCalc 2.0.0, NetworkX 3.5 and a supported MILP solver, the release and original pipeline audit can be repeated with the pinned checkout containing its backup graph6 blob.

```bash
python audit.py /absolute/path/to/AutoGraphForge
```
