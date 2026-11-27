# AutoGraphForge row 2527

**Disproved. The upstream release already contains counterexamples.** Ján Pastorek's normalized physical row 2527 (ID `1bc05f9a`, four touches) proposes that every nontrivial bipartite graph G satisfies

```text
minimum maximal matching size ≤ (3/4) · independent domination number + 11/2.
```

An 18-vertex crown graph in the pinned graph6 backup has values 8 and 2, giving the false inequality 8 ≤ 7. The Lean file `Crown.lean` certifies both optima for the entire crown family. A separate 18-vertex **planar** counterexample is formed by eight internally disjoint three-edge paths with common ends. This second construction proves a stronger statement: even for connected bipartite planar graphs, no function of the independent domination number bounds the minimum maximal matching size. [Pinned survivor](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L2527) · [Archived 18-vertex crown, physical graph6 line 1124](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/backup_20260730T150317/graphs.g6#L1124)

## Planar family and the threshold at one

Take two hubs a and b and k ≥ 1 paths a–uᵢ–vᵢ–b. The hubs are independent and dominate every vertex. For any proposed single dominating vertex, the hub on the opposite side is distinct from it and nonadjacent to it. Thus the independent domination number is exactly two.

The k middle edges form a maximal matching and dominate every edge. Each graph edge meets only one of those middle edges, so every edge-dominating set has at least k edges. Both the line-graph domination number and the minimum maximal matching size are exactly k. The two parts are {a, v₁, …, vₖ} and {b, u₁, …, uₖ}. The row 659 straight-line drawing places the ith path at (0,0), (1,i), (2,i), (3,0). Open edges occupy three successive vertical strips, with distinct horizontal levels in the middle strip.

The right side of the catalogue inequality equals seven for every k. Setting k = m+8 gives excess m+1. More strongly, given any proposed upper bound f, take k = f(2)+1. The family theorem and the arbitrary-function statement are `ThetaIndependent2527.family` and `no_bound`.

For a nontrivial bipartite graph with independent domination number **one**, a single vertex is adjacent to every other vertex. Bipartiteness prevents any two of its neighbors from being adjacent, so the graph is a star and both edge optima are one. The theorem `bipartite_one` verifies this boundary. The star characterization is elementary and extends to triangle-free graphs.

## Earlier witnesses and prior results

The pinned record was still labeled proposed, with a null Lean proof. Its ID and its exact normalized statement were absent from the three released refutation files, the verified Lean proofs and the inspected maths index. The released data nevertheless include explicit graphs violating the row. A status label alone would give a misleading account of this result. [Upstream results](https://github.com/JanPastorek/AutoGraphForge/tree/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results) · [Inspected index](https://github.com/vjdad4m/maths/blob/0511dc22e4667ee2fbfb613d924f2616e8a81250/README.md)

On the crown K_{t,t} with a perfect matching removed, t ≥ 3, one omitted pair is an independent dominating set. No singleton dominates. Every vertex has degree t−1. Row 1078's triangle-free minimum-degree bound gives edge domination at least t−1. Leave one omitted pair unmatched and cyclically shift the other t−1 indices to obtain a maximal matching of that size. Hence both edge optima equal t−1. The audit explicitly labels each vertex by its part and omitted partner, verifies the full crown adjacency matrix, and checks the backup's graph6 code at line 1124. It is the t = 9 instance of the kernel-checked family.

More simply, on K_{t,t} every maximal matching is perfect and an independent dominating set is a whole part. Their common value t violates the row for t ≥ 23. Thus the catalogue disproof already follows from standard elementary facts. The sparse planar family gives the fixed-parameter conclusion subject to a further class restriction. Historical priority for that observation is unverified. Independent domination and edge domination are classical parameters. [Goddard and Henning on independent domination](https://doi.org/10.1016/j.disc.2012.11.031) · [Yannakakis and Gavril on edge domination](https://doi.org/10.1137/0138030) · [Earlier balanced-biclique matching proof](https://github.com/vjdad4m/maths/tree/0511dc22e4667ee2fbfb613d924f2616e8a81250/autographforge-1883)

## Source conventions and audit

GraphCalc 2.0.0 uses NetworkX bipartiteness, allows disconnected graphs and requires order at least two for nontriviality. Its independent-domination ILP minimizes the number of selected vertices, forbids selecting both endpoints of any edge, and requires every closed neighborhood to meet the selection. Its matching wrapper calls vertex domination on the NetworkX line graph. The Lean statement uses exact rational coefficients, Mathlib two-colorability, `IsIndepSet`, closed-neighborhood domination and Mathlib's actual line graph. It separately certifies the minimum size of an inclusion-maximal matching. [Graph classes](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/core/basics.py) · [Independent-domination implementation](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/invariants/domination.py#L313-L444) · [Matching implementation](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/invariants/domination.py#L1454-L1489)

The 312 graph6 encodings from three refutation files and 4,700 backup encodings have 4,776 distinct codes in their union. Of these 1,223 are eligible. The numerical audit found **54 violating encodings**, including 15 crowns with 9 through 23 vertices per side. Eleven of the 54 occur in the refutation files under other claims. None of the 54 is planar. Counts apply to graph6 encodings and the pinned files. The two infinite families are proved independently of this numerical experiment.

The audit checks the integer comparison 4m ≤ 3i+22. It first tries a greedy maximal matching upper bound and the Slater lower bound on i. For the remaining graphs it recognizes crowns, uses GraphCalc's independent-domination optimizer, and checks degree or edge-neighborhood bounds where applicable. For undecided cases it directly tests maximal matching feasibility at t = ⌊(3i+22)/4⌋. A maximal matching can be augmented to any size up to a maximum matching while keeping previously matched vertices covered. For a size-t matching on a bipartition L, R, enumerate the unmatched set U in L. The matching must saturate L−U and must cover N(U) in R. These conditions can be tested separately in the graph obtained by deleting U. Start with a matching covering N(U) and augment it until it covers L−U. The unmatched vertices are then independent. The audit cross-checks this test against exhaustive matching enumeration on every one of the 512 labeled subgraphs of K₃,₃. It also calls the upstream optima on parallel-path examples with k = 1, 2, 7, 8 and 12.

## Reuse and replay

Five bundled modules are unchanged from the row 659 source closure. `Theta.lean` and `ThetaDrawing.lean` give the parallel-path construction, edge packing argument, matching, two-coloring and plane drawing. `Row1078.lean` and `Bound.lean` provide the line-graph optimizer, attainment and triangle-free minimum-degree lower bound. `MatchingBasis.lean` includes endpoint-support and matching lemmas from rows 371 and 1883. The new files are `Independent.lean`, `Crown.lean` and `Row2527.lean`. [Row 1078](https://github.com/vjdad4m/maths/tree/0511dc22e4667ee2fbfb613d924f2616e8a81250/autographforge-1078) · [Row 574](https://github.com/vjdad4m/maths/tree/0511dc22e4667ee2fbfb613d924f2616e8a81250/autographforge-574)

Run from the extracted source with Lean 4.19.0 on PATH and a prepared Mathlib v4.19.0 checkout at `c44e0c8ee63ca166450922a373c7409c5d26b00b`.

```bash
MATHLIB_DIR=/absolute/path/to/mathlib4 bash replay.sh
```

The script compiles all eight modules from source in a fresh directory with warnings as errors and checks the printed axiom lists for eight result theorems. Only `propext`, `Classical.choice` and `Quot.sound` occur. With GraphCalc 2.0.0, NetworkX 3.5 and a supported MILP solver such as CBC, reproduce the source and numerical audit with

```bash
python audit.py /absolute/path/to/pinned/AutoGraphForge
```

The checkout must include the pinned graph6 Git blobs. Expected outputs are in `Replay.log` and `SourceAudit.log`.
