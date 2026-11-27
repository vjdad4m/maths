# AutoGraphForge row 2560 and induced bull packings

**Row 2560 holds on its full numerical domain, and the factor three is sharp.** Ján Pastorek’s normalized physical row 2560 states that for a nontrivial chordal claw-free graph the edge cover number is at most three times the minimum maximal matching number. The five-vertex bull attains equality. It is a triangle with a leaf attached to each of two different triangle vertices. The selected edge joining those two attachment vertices dominates every edge, while covering all five vertices requires three edges. [Pinned row 2560, ID 6d159443](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L2560)

For every finite isolate-free claw-free graph, write ρ for the minimum edge cover size, γₑ for the minimum edge domination size, and b for the maximum number of pairwise vertex-disjoint induced bulls. Edges between different bulls are allowed. The stronger theorem is

**ρ ≤ 2γₑ + min(γₑ, b).**

This holds across disconnected graphs and requires no chordality. Lean proves that b = 0 exactly when the graph has no induced bull, and that b ≤ ⌊|V|/5⌋. On the bull the three optimizer values (ρ, γₑ, b) are (3, 1, 1). In particular the correction to the factor-two bound can be necessary even on a connected chordal graph.

## Proof

Take any edge-dominating set D. Its endpoints meet every edge, so the vertices outside its endpoints form an independent set. Assign each outside vertex to one selected edge with an adjacent endpoint. An incident edge for every vertex exists by isolate-freeness. For a selected edge ab, write X for its assigned vertices.

Any two distinct vertices of X can be paired with different endpoints. Otherwise both would see only a, or both only b, forming a claw with the other endpoint. Also |X| ≤ 3. If b sees every vertex of X, claw-freeness allows at most two. If b misses x, the pairing property forces b to see every other vertex of X, again at most two.

If |X| ≤ 2, two edges suffice to cover a, b and X. If |X| = 3, each endpoint misses some assigned vertex. Choose x seen only by a and y seen only by b. The third vertex z sees both endpoints by pairing first with x and then with y. Thus a, b, x, y and z induce a bull and can be covered by three edges.

The bulls arising this way are vertex-disjoint, even when two selected edges in D share an endpoint. The assigned sets are disjoint by construction and contain no selected endpoints. If two selected edges with three assignments shared an endpoint, it would see two assigned vertices from the first edge and one from the second. These three independent neighbors would induce a claw.

Taking the union of the covers costs at most 2|D| plus the number of selected edges with three assignments. This number is at most both |D| and b. Minimize over D.

## Provenance and exact domain

At the audit the upstream default branch was at `4d1a8afc99447cacd2328cca20e47b6493e8dbc5`. The row had three normalized touches and the label `promising:class`. The CEGIS record said `proposed` with a null Lean proof. Its statement and ID were absent from the three refutation lists and the verified Lean files. The public maths README at `a82680e1640398c4f7417f4c37eb9605e8f714ea` listed neither the row number nor the ID. The sole public upstream issue concerned a different conjecture. [Pinned results](https://github.com/JanPastorek/AutoGraphForge/tree/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results) · [Shared index at inspection](https://github.com/vjdad4m/maths/blob/a82680e1640398c4f7417f4c37eb9605e8f714ea/README.md) · [Upstream issue](https://github.com/JanPastorek/AutoGraphForge/issues/1)

GraphCalc 2.0.0 uses order at least two for `nontrivial`, tests chordality with NetworkX and checks for three mutually nonadjacent neighbors for `claw_free`. Lean uses exclusion of induced Mathlib cycle graphs of lengths at least four and exclusion of an induced claw. GraphCalc implements `min_maximal_matching_number` by domination on the line graph. The Lean optimizer uses the same graph and objective. Equivalence with the minimum cardinality of a maximal matching is classical. [Class predicates](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/core/basics.py) · [Matching wrapper](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/invariants/domination.py#L1464-L1490) · [Yannakakis and Gavril](https://doi.org/10.1137/0138030)

NetworkX requires an edge cover to meet every vertex. A graph with an isolate has no edge cover. GraphCalc raises on such input and the pinned battery leaves the cell missing. The row theorem quantifies over each returned numerical value. The audit exercised the public battery on the triangle, the bull and two isolated vertices. Among all 4,776 distinct graph6 encodings in the three refutation files and four identical backup lists, 953 met the three class predicates. Of those, 354 had isolates and 599 had numerical values. For all 599 the actual edge cover size was already at most three times a componentwise lower bound on edge domination, certified by counting edges incident to a selected edge. Two backup encodings give the sharp bull. [Edge cover wrapper](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/invariants/classics.py#L628-L655) · [Upstream battery](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/pipeline/invariants_graphcalc.py) · [Archived bull](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/backup_20260730T150317/graphs.g6#L78)

The work extends the locally checked row 1125 hereditary claw/bull argument by assigning each outside vertex once and proving disjointness of the bulls. The catalogue statements are distinct. The bull satisfies row 2560’s hypotheses and violates the factor-two inequality. Prior literature includes the structure theorem for claw- and bull-free graphs, Sumner’s perfect matching theorem for connected even-order claw-free graphs, and a comparison between ordinary vertex domination and edge domination for claw-free graphs of minimum degree at least two. Targeted searches for the edge cover/edge domination bound and the disjoint induced bull correction found no earlier statement of the packing inequality. Historical priority remains unverified. [Claw/bull-free structure](https://arxiv.org/abs/1901.00043) · [Sumner, Graphs with 1-factors](https://scholarcommons.sc.edu/cgi/viewcontent.cgi?article=1025&context=math_facpub) · [Domination versus edge domination on claw-free graphs](https://doi.org/10.1016/j.dam.2023.05.002)

## Source closure and replay

`Row1078.lean` supplies the published line-graph optimizer and its shared-endpoint characterization. `MatchingBasis.lean` and `Proof137.lean` are inherited dependencies. The row 1125 modules supply the forbidden patterns, edge cover definitions and exact small bull values. In the local copy of `Local.lean`, `small_piece` extracts the existing two-edge construction under the cardinality hypothesis used in its proof. The original theorem is preserved as a corollary. `Patch.lean` treats three assignments, `Packing.lean` proves the quantitative inequality, and `Row2560.lean` checks the catalogue row, sharpness and elementary packing facts. [Published line-domination code](https://github.com/vjdad4m/maths/blob/a82680e1640398c4f7417f4c37eb9605e8f714ea/autographforge-1078/Row1078.lean)

With Lean 4.19.0 on PATH and Mathlib 4.19.0 at commit `c44e0c8ee63ca166450922a373c7409c5d26b00b` built locally, run from the extracted source directory

```bash
MATHLIB_DIR=/absolute/path/to/mathlib4 bash replay.sh
```

The script builds all ten modules into a fresh temporary directory, uses warnings as errors, and checks the printed axiom lists for seven theorems. The expected lists contain only `propext`, `Classical.choice` and `Quot.sound`. The proof uses kernel reduction for fixed finite verifications. For the separate dataset check, use GraphCalc 2.0.0 and NetworkX 3.5 with a supported MILP solver and the pinned upstream checkout including the graph6 backup blob.

```bash
python audit.py /absolute/path/to/AutoGraphForge
```
