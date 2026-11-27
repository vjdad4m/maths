# AutoGraphForge row 1125

**Proved on the full numerical domain.** Ján Pastorek’s normalized physical row 1125 states that a nontrivial claw-free cograph has edge cover number at most twice its minimum maximal matching number. The triangle attains equality, with values 2 and 1. [Pinned row 1125, ID 65f2978c](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L1125)

**The claw and the bull are exactly the hereditary obstructions.** For a graph G, the following are equivalent.

1. Every finite induced subgraph H with no isolated vertices satisfies ρ(H) ≤ 2γₑ(H), where ρ is the minimum edge cover size and γₑ the minimum edge domination size.
2. G contains neither an induced claw nor an induced bull.

The claw is K₁,₃. The bull consists of a triangle with a leaf attached to each of two distinct triangle vertices. Each obstruction has ρ = 3 and γₑ = 1. Cographs exclude the bull because its two leaves and their attachment vertices induce P₄. The equivalence concerns the inequality on **all** qualifying induced subgraphs. The theorem includes disconnected graphs.

## Proof

An edge cover meets every vertex. An edge-dominating set meets every edge, meaning that each graph edge shares an endpoint with a selected edge, possibly itself. Fix any edge-dominating set D, and let S be all its endpoints. The vertices outside S are independent. Since there are no isolates, each outside vertex is adjacent to an endpoint in S.

For a selected edge ab, let X be the outside vertices adjacent to a or b. In a claw-free graph any two distinct x,y in X can be paired to different endpoints of ab. Indeed, the only way two such vertices could fail to have distinct representatives is for both to see just the same endpoint. That endpoint would be the center of a claw on x,y and the opposite endpoint.

Suppose X has at least three vertices. Neither a nor b can see all of X, since three of those neighbors would form the leaves of a claw. Pick x adjacent only to a and y adjacent only to b. A third vertex z must see b by the pairing property for x,z, and must see a by the same property for y,z. These five vertices induce a bull. In the absence of both obstructions, |X| ≤ 2.

At most two graph edges therefore cover a,b and X. For two outside vertices use their pairs to different endpoints. For one, use ab and one incident edge to the outside vertex. For zero, use ab. Taking the union over D covers all vertices and uses at most 2|D| edges. Minimizing over D proves sufficiency. The two small obstruction values prove necessity. The construction works even when two selected edges in D share an endpoint, so the proof applies directly to the optimizer in the catalogue implementation.

## Numerical domain and provenance

The row has 61 normalized touches and the annotation `promising:class`. Its pinned CEGIS record has status `proposed` and a null Lean proof. Neither the ID nor the statement appears in the three refutation JSON files or the verified Lean files. The public maths index at `cd23ea9` contained no row 1125 entry on 27 November 2026. The sole upstream issue visible at inspection concerns another ID. [Pinned results](https://github.com/JanPastorek/AutoGraphForge/tree/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results) · [Inspected shared index](https://github.com/vjdad4m/maths/blob/cd23ea9deadf98a0adfb53607c402d1b952670e2/README.md) · [Upstream issue](https://github.com/JanPastorek/AutoGraphForge/issues/1)

GraphCalc 2.0.0 uses order at least two for nontriviality, an independent triple in an open neighborhood for an induced claw, and P₄-freeness for cographs. Its matching parameter calls vertex domination on the NetworkX line graph. The equivalence with minimum maximal matching size is classical. Lean uses the very same line-graph optimizer, with vertices given by actual unordered graph edges. [GraphCalc classes](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/core/basics.py) · [GraphCalc matching wrapper](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/invariants/domination.py#L1454-L1489) · [Yannakakis and Gavril on edge domination](https://doi.org/10.1137/0138030)

GraphCalc computes ρ by taking the size of `networkx.min_edge_cover`. If a vertex is isolated, an edge cover does not exist and NetworkX raises. AutoGraphForge’s per-invariant recovery leaves that cell missing. The audit exercises the public pinned `compute_battery` entry point on the triangle and on two isolated vertices. Lean represents a missing value by `none`. The row theorem applies to each actual numerical value, and `coverable_iff` proves that existence of an edge cover is equivalent to absence of isolates. [Edge-cover implementation](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/invariants/classics.py#L599-L653) · [Upstream battery](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/pipeline/invariants_graphcalc.py#L60-L159)

The audit inspected all 4,776 distinct graph6 encodings in the union of the three refutation files and four identical backups. Of 652 satisfying the row’s graph predicates, 329 contained isolates and 323 had a numerical edge cover value. All 323 satisfied the row. For 316, the computed edge cover was at most twice a componentwise lower bound on edge domination obtained by counting the number of edges a single edge can meet. The other seven were checked using GraphCalc’s line-graph optimizer. The archived claw and bull illustrate the forbidden configurations in the stronger result. [Archived claw at line 73](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/backup_20260730T150317/graphs.g6#L73) · [Archived bull at line 78](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/backup_20260730T150317/graphs.g6#L78)

González Hermosillo de la Maza, Jing and Masjoody previously classified the structure of connected (claw,bull)-free graphs. The short local argument here gives an invariant characterization of this established class. Targeted literature and repository searches found no earlier statement of this exact hereditary inequality characterization. Historical priority remains unverified. [Prior classification](https://arxiv.org/abs/1901.00043)

## Files and replay

Three dependencies were checked byte-for-byte against the shared repository. `Proof137.lean` supplies the induced-path definition used for cographs. `Row1078.lean` supplies `lineDomination` and its shared-endpoint characterization. `MatchingBasis.lean` is the published dependency of that module. `Patterns.lean` uses Mathlib induced graph embeddings for the claw and bull. `Local.lean` proves the two-edge construction around one selected edge. `Cover.lean` proves the general bound and exact row. `Obstructions.lean` proves the hereditary equivalence and the sharp triangle example. Only the fixed small-graph certificates use finite enumeration. [Published P₄ definition](https://github.com/vjdad4m/maths/blob/cd23ea9deadf98a0adfb53607c402d1b952670e2/autographforge-cograph/Proof137.lean) · [Published line-graph definition](https://github.com/vjdad4m/maths/blob/cd23ea9deadf98a0adfb53607c402d1b952670e2/autographforge-1078/Row1078.lean)

With Lean 4.19.0 on PATH and a prepared Mathlib 4.19.0 checkout at `c44e0c8ee63ca166450922a373c7409c5d26b00b`, extract the source archive and run

```bash
MATHLIB_DIR=/absolute/path/to/mathlib4 bash replay.sh
```

The script rebuilds all seven modules in a fresh temporary directory with warnings as errors. It checks the printed axiom lists for eight result theorems. Only `propext`, `Classical.choice` and `Quot.sound` occur. To repeat the source and numerical audit, install GraphCalc 2.0.0, NetworkX 3.5 and a supported MILP solver such as CBC, then run

```bash
python audit.py /absolute/path/to/pinned/AutoGraphForge
```

The checkout must contain the graph6 backup blob. Expected outputs appear in `Replay.log` and `SourceAudit.log`.
