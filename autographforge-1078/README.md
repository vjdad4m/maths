# AutoGraphForge row 1078

**Proved.** Every finite simple, regular, triangle-free graph with at least two vertices has average degree at most its minimum maximal matching number. Equality occurs at every positive degree d, on K_{d,d}. Disconnected graphs and degree-zero regular graphs are included. This is Ján Pastorek's normalized physical row 1078, ID `99304c0e`, with 68 touches and label `promising:class`. [Pinned survivor](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L1078)

## Proof

In fact, every edge-dominating set D in a nonempty finite simple triangle-free graph has size at least the minimum degree. Choose a vertex x outside the endpoints of D if there is one. Then each edge xy must be dominated at y, so each neighbor of x belongs to some edge in D. If D covers every vertex, choose any x and the same conclusion holds. Assign each neighbor of x to a selected edge containing it. Two distinct neighbors cannot belong to the same edge, because they would form a triangle with x. This assignment is injective, proving δ(G) ≤ deg(x) ≤ |D|.

The edges of any maximal matching dominate all edges. In a d-regular graph both the minimum and average degree equal d. On K_{d,d}, the d diagonal edges are a maximal matching and the lower bound forces equality. The average-degree statement can fail without regularity, as P₃ has average degree 4/3 and minimum maximal matching number 1. It can also fail without triangle-freeness, as K₃ has average degree 2 and minimum maximal matching number 1.

## Formal scope and reuse

GraphCalc 2.0.0 implements `min_maximal_matching_number(G)` by calling `domination_number(nx.line_graph(G))`. Its regularity predicate is NetworkX regularity, its nontriviality predicate checks order at least two and it computes average degree by dividing the sum of the degrees by the order. The Lean theorem `row1078` proves the bound for both the closed-neighborhood domination optimum of Mathlib's actual line graph and the minimum cardinality of an inclusion-maximal matching. The former optimizes over arbitrary sets of edges, allowing common endpoints. A matching is inclusion-maximal exactly when no edge has both ends outside its support. [GraphCalc matching wrapper](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/invariants/domination.py#L1454-L1489) · [Domination ILP](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/invariants/domination.py#L84-L170) · [Average degree](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/invariants/degree.py#L113-L139) · [Class predicates](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/core/basics.py)

`degree_le_of_dominating` constructs the local injection. `minDegree_le_lineDomination` specializes it to an optimum. `sharp` proves that both optima and the average degree equal d on every balanced biclique of positive degree. The boundary computations on P₃ and K₃ are independently reproduced in GraphCalc.

`MatchingBasis.lean` extracts the published row 371 matching-size, endpoint-support and extension lemmas, and the published row 1883 maximal-matching predicate, balanced-biclique graph, exact matching number and regularity proof. The clique-cover characterization in row 1160 concerns perfect matchings. Row 1078 instead needs all maximal matchings, including ones that leave vertices uncovered. It uses the same three-adjacency triangle-free predicate as row 1160. [Published row 371](https://github.com/vjdad4m/maths/blob/0965fd58d3027e10c30295a29229aad7d9cb1779/autographforge-371/AutoGraphForge371.lean) · [Published row 1883](https://github.com/vjdad4m/maths/blob/0965fd58d3027e10c30295a29229aad7d9cb1779/autographforge-1883/AutoGraphForge1883.lean)

## Status and attribution

The pinned release lists the row as proposed with a null Lean proof. Its ID and exact statement were absent from the released refutations and verified proofs, the inspected public maths index had no row 1078 entry, and upstream issue 1 concerns another ID. This audit establishes the status of those sources. Historical priority for the elementary degree bound is unverified. [Release results](https://github.com/JanPastorek/AutoGraphForge/tree/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results) · [Inspected public index](https://github.com/vjdad4m/maths/blob/0965fd58d3027e10c30295a29229aad7d9cb1779/README.md) · [Upstream issue](https://github.com/JanPastorek/AutoGraphForge/issues/1)

Edge domination and minimum maximal matching are classical. Yannakakis and Gavril studied their equivalence, and Song, Miao, Wang and Zhao studied these optima on complete multipartite graphs. Caro, Davila, Henning and Pepper's Theorem 3.2 gives a related lower bound δn/[2(Δ+δ−1)]. For K_{3,3} this gives 9/5 before integer rounding, leaving a gap to the required 3. The sharper step here uses triangle-freeness to make the map from one neighborhood injective. [Yannakakis and Gavril (1980)](https://doi.org/10.1137/0138030) · [Song et al. (2014)](https://doi.org/10.1080/00207160.2013.818668) · [Caro et al., Theorem 3.2](https://arxiv.org/pdf/2104.01092)

The three refutation files and the four identical graph6 backups contain 4,776 distinct encodings. Of these, 313 meet the row hypotheses, including 72 from the refutation files. For 255 graphs, degree zero or a count of the edges one selected edge can dominate suffices. For the other 58, the audit checks that fewer than d edges must leave a vertex uncovered and that every edge meets each neighborhood in at most one vertex. All 313 satisfy the bound. Eight representative calls to the original GraphCalc optimizer cover the zero-degree case, equality, strict inequality and the two failed weakenings. [Backup graph data](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/backup_20260730T150317/graphs.g6)

## Replay

Use Lean 4.19.0 on PATH and Mathlib v4.19.0 at `c44e0c8ee63ca166450922a373c7409c5d26b00b`. With a partial Mathlib cache, build the `Mathlib.Combinatorics.SimpleGraph.LineGraph` module in that checkout. From the extracted source run

```bash
MATHLIB_DIR=/absolute/path/to/mathlib4 bash replay.sh
```

The script compiles both modules from source in a fresh directory with warnings as errors and checks five printed axiom lists against `propext`, `Classical.choice` and `Quot.sound`. For the independent release and numerical audit, use GraphCalc 2.0.0, NetworkX 3.5 and a supported MILP solver, then run

```bash
python check_source.py /absolute/path/to/pinned/AutoGraphForge
```
