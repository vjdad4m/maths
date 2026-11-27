# AutoGraphForge row 659

**Disproved, with an unbounded gap on connected bipartite planar graphs.** Ján Pastorek's normalized physical row 659 proposes that every nontrivial planar triangle-free graph satisfies

```text
minimum maximal matching size + 1 ≤ Roman domination number.
```

Take four internally disjoint paths of length three with the same two ends. This simple graph has ten vertices, minimum maximal matching size four and Roman domination number four. The proposed inequality would require 5 ≤ 4. The catalogue ID is `2763b0fb`, with 136 touches and label `promising:class`. [Pinned row](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L659)

## The family and its exact values

For each k ≥ 2, take hubs a and b and paths a–uᵢ–vᵢ–b, one for each of k indices. This gives 2k+2 vertices. The two color classes are {a, v₁, …, vₖ} and {b, u₁, …, uₖ}. For a straight-line plane drawing, put a at (0,0), b at (3,0), uᵢ at (1,i) and vᵢ at (2,i). The interiors of the three kinds of edge lie in separate open vertical strips. Within a strip, the middle edges occupy distinct levels and the spokes share only a hub. The Lean drawing checks embedded arcs, reversal, avoidance of every vertex by each open edge, and disjoint open arcs for distinct undirected edges.

**Minimum maximal matching size and edge domination number both equal k.** The k middle edges are an induced matching. Every other edge meets exactly one of them, so this matching is maximal and edge-dominating. Conversely, an edge can dominate at most one of the middle edges. Every edge-dominating set therefore needs at least k members. The reusable lemma `packing_lower` makes this last argument for any designated family of edges with the same separation property.

**Roman domination number equals four.** Giving label two to both hubs and zero to every other vertex is feasible. To prove optimality, partition the graph into the side consisting of a and the uᵢ, and the side consisting of b and the vᵢ. If one side has weight at most one, then its hub cannot have label zero because it would require a neighbor of label two on that side. Thus its hub has label one and all the other vertices on that side have label zero. Each corresponding internal vertex on the opposite side must have label two. That side alone has weight at least 2k ≥ 4. If both sides have weight at least two, the same lower bound follows.

The theorem `Theta659.family` proves the two graph classes, connectivity, order, and both matching interpretations together with the Roman optimum. For k ≥ 4 the arithmetic excess is exactly k−3, while the proposed right-hand side stays fixed at four. The four-path graph is the first violation within this family. No search for the smallest counterexample among all graphs is part of this result.

## Source conventions and attribution

GraphCalc 2.0.0 computes `min_maximal_matching_number(G)` by vertex domination of the NetworkX line graph. Lean uses Mathlib's actual line graph, then separately proves the minimum size of an inclusion-maximal matching. The Roman optimizer assigns mutually exclusive binary variables for labels one and two at each vertex. A vertex with neither label needs a neighboring vertex with label two. The objective is the sum of the vertex labels. Nontrivial means at least two vertices. The planarity wrapper uses NetworkX planarity, and triangle-freeness excludes three pairwise adjacent vertices. [Matching wrapper](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/invariants/domination.py#L1454-L1489) · [Roman optimizer](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/invariants/domination.py#L783-L923) · [Graph classes](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/core/basics.py)

The construction is the classical generalized theta family with all paths of length three. The equality of edge domination number and the size of a dominating induced matching is a standard consequence, also stated by Mahmoodi, Behmaram, Došlić and Asadi. Their Theorem 33 addresses Roman labels on the edges. Row 659 uses the vertex Roman domination parameter studied by Cockayne, Dreyer, Hedetniemi and Hedetniemi. Our targeted literature and repository checks did not locate an earlier explicit row 659 disproof. Historical priority for the family calculation is unverified. [Generalized theta graph definition](https://www.sciencedirect.com/science/article/abs/pii/S0012365X22001716) · [Dominating induced matchings](https://doi.org/10.1080/09728600.2024.2342310) · [Roman domination in graphs](https://doi.org/10.1016/j.disc.2003.06.004)

The row 574 distinguished-edge argument supplies the model for `packing_lower`. The bundled `MatchingBasis.lean`, `Row1078.lean` and `Bound.lean` are unchanged from the row 574 closure. They supply the matching predicates, line-graph coverage by shared endpoints and attainment of the minimum. `ThetaDrawing.lean` adapts the row 464 plane drawing predicate, segment paths, orientation and embedding proof. `Roman.lean` reuses the Roman-label and optimum definitions of row 621. [Row 574](https://github.com/vjdad4m/maths/tree/04abc690197f91c371057ca1f3b55557037ecc41/autographforge-574) · [Row 464](https://github.com/vjdad4m/maths/tree/04abc690197f91c371057ca1f3b55557037ecc41/autographforge-464) · [Row 621](https://github.com/vjdad4m/maths/tree/04abc690197f91c371057ca1f3b55557037ecc41/autographforge-621)

## Release audit

The inspected upstream HEAD matched pin `4d1a8afc99447cacd2328cca20e47b6493e8dbc5`. The exact row was proposed with a null proof. Its ID and statement were absent from the three released refutation files and the verified Lean proofs. The shared maths README at `04abc690` had no row 659 entry. Upstream issue 1 concerns a different ID. [Pinned results](https://github.com/JanPastorek/AutoGraphForge/tree/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results) · [Inspected maths index](https://github.com/vjdad4m/maths/blob/04abc690197f91c371057ca1f3b55557037ecc41/README.md) · [Upstream issue](https://github.com/JanPastorek/AutoGraphForge/issues/1)

The release audit combined 312 distinct refutation graph6 encodings with 4,700 backup encodings. There were 4,776 distinct encodings in their union, of which 957 satisfied the hypotheses, including 115 from the refutation files. None violated row 659 in the numerical audit. For each eligible graph, the script computes the Roman optimum using GraphCalc and builds maximal matchings as upper bounds for the left parameter. When that test is inconclusive it invokes the GraphCalc matching optimizer. As positive controls it reproduces the matching/Roman values (2,4), (3,4), (4,4) and (7,4) on the 2-, 3-, 4- and 7-path graphs. The Lean disproof and exact family formulas are independent of these optimizer runs.

## Replay

From the extracted source, with Lean 4.19.0 on PATH and a prepared Mathlib v4.19.0 checkout at `c44e0c8ee63ca166450922a373c7409c5d26b00b`, run

```bash
MATHLIB_DIR=/absolute/path/to/mathlib4 bash replay.sh
```

The script builds all seven modules into a fresh temporary directory with warnings as errors and checks the six printed result axiom lists against `propext`, `Classical.choice` and `Quot.sound`. For a partial dependency cache, ensure that the Mathlib imports from the seven files, including `Mathlib.Combinatorics.SimpleGraph.LineGraph` and `Mathlib.Topology.Path`, are built. The independent numerical audit uses GraphCalc 2.0.0, NetworkX 3.5, and a supported MILP solver such as CBC. It reads the pinned Git checkout, including the graph6 backup objects.

```bash
python check_source.py /absolute/path/to/pinned/AutoGraphForge
```

The expected outputs are in `Replay.log` and `SourceAudit.log`.
