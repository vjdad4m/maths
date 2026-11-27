# AutoGraphForge row 1531 and its connected equality cases

**Every nontrivial, triangle-free, claw-free graph with a numerical edge cover value satisfies ρ ≤ 2γₑ. Among connected graphs, equality holds exactly for the paths P₃, P₄, and P₇.** Here ρ is the minimum edge cover size and γₑ is the minimum edge domination size, the value returned by GraphCalc for `min_maximal_matching_number`. The optimal pairs (ρ, γₑ) on the three paths are (2,1), (2,1), and (4,2), respectively. The inequality includes disconnected graphs. [Ján Pastorek’s normalized physical row 1531](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L1531)

## Proof and attribution

The inequality is a direct application of the previously checked row 2560 packing bound ρ ≤ 2γₑ + min(γₑ, b), where b is the largest number of vertex-disjoint induced bulls. Every bull contains a triangle, so b vanishes. Row 1125’s claw/bull hereditary theorem also gives the factor two directly. The triangle-free and cograph hypotheses are distinct, and the 7-vertex path is a sharp example for row 1531 containing an induced 4-vertex path.

For the equality claim, let G be connected of order n ≥ 2. The neighbors of each vertex are independent by triangle-freeness, so three neighbors would induce a claw. Thus G has maximum degree at most two and is a path or a cycle. Pair consecutive vertices along its spanning path, covering the last vertex with the previous edge’s neighboring edge if necessary. This takes ⌈n/2⌉ edges. Every edge meets just two vertices, which gives the reverse inequality. [Reused degree-two classification](https://github.com/vjdad4m/maths/blob/1a203bc03c27b831ed6d3662cb05a572dbbe19dd/graffiti-183/src/DegreeTwoClass.lean)

Set k = γₑ. Each selected edge meets at most three edges including itself, because each endpoint has degree at most two. Therefore |E| ≤ 3k. Connectivity gives n − 1 ≤ |E|. At equality, ⌈n/2⌉ = 2k, so n is either 4k − 1 or 4k. The inequalities and n ≥ 2 leave only (n,k) = (3,1), (4,1), or (7,2). A 3-cycle is a triangle. A 4-cycle or 7-cycle has n edges, exceeding 3k in the corresponding case. Thus each equality graph is one of the three paths. On zero-based path vertices, edge 0–1 dominates P₃, edge 1–2 dominates P₄, and edges 1–2 and 4–5 dominate P₇. This proves the converse and the exact values.

The classification also follows from known formulas. Cariolaro and Fu give the minimum size of a maximal matching of a path as ⌈(n − 1)/3⌉ and of a cycle as ⌈n/3⌉ in Proposition 6, using the equivalent augmentation number from Proposition 5. The present work is a catalogue application and a Lean verification of the equality cases. The Lean proof derives the bounds and checks the small cases independently. [Cariolaro and Fu, *Covering graphs with matchings of fixed size*](https://doi.org/10.1016/j.disc.2008.09.031) · [Yannakakis and Gavril, *Edge Dominating Sets in Graphs*](https://doi.org/10.1137/0138030)

## Upstream status, definitions and corpus

At inspection the upstream default branch was at `4d1a8afc99447cacd2328cca20e47b6493e8dbc5`. Its CEGIS record `e88c1f88` was marked `proposed` and had a null Lean proof. The normalized row had 39 touches and label `promising:class`. Its statement and ID were absent from the three refutation files and the verified Lean sources. The public maths index at `1a203bc03c27b831ed6d3662cb05a572dbbe19dd` did not list row 1531 or its ID. The sole upstream issue concerned a different conjecture. [CEGIS release](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/cegis_results.json) · [Inspected shared index](https://github.com/vjdad4m/maths/blob/1a203bc03c27b831ed6d3662cb05a572dbbe19dd/README.md) · [Upstream issue](https://github.com/JanPastorek/AutoGraphForge/issues/1)

GraphCalc 2.0.0 takes nontrivial to mean at least two vertices. It tests for three mutually nonadjacent neighbors at a vertex to recognize a claw, and tests for three vertices forming a triangle. The edge cover routine calls NetworkX minimum edge cover. The matching parameter uses minimum vertex domination of the line graph. In the presence of isolates, NetworkX raises and AutoGraphForge leaves the edge cover cell missing. Lean models this with an optional value, and the exact row applies to each returned number. [GraphCalc class implementations](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/core/basics.py) · [Edge cover wrapper](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/invariants/classics.py#L628-L655) · [Minimum maximal matching wrapper](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/invariants/domination.py#L1464-L1490)

The audit covered 4,776 distinct graph6 encodings in the refutation releases and four graph backups. Of 414 encodings satisfying the three graph predicates, 209 had an isolate and 205 had numerical values. Direct evaluation of both optimizers verified the inequality on all 205. Of the 91 connected numerical encodings, five were equality examples, representing the three paths. P₇ appears on backup line 302. The pinned public `compute_battery` entry point reproduced the three sharp pairs, the strict C₄ case (2,2), and the missing edge cover value for two isolates. [Archived P₇](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/backup_20260730T150317/graphs.g6#L302) · [Battery entry point](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/pipeline/invariants_graphcalc.py)

## Source and replay

`Bounds.lean` contains `EdgeCover1531.row1531`, the incidence bound and the restriction on equality orders. `IsoCover.lean` proves invariance of both optimizers under graph isomorphism. `Equality.lean` proves `EdgeCover1531.equality_iff`. `Examples.lean` proves the exact connected edge cover formula and the catalogue hypotheses and numerical values for the three sharp paths. The bundle includes the row 2560 source closure and the Graffiti.pc #183 degree-two classification with its dependencies. The included `DegreeTwoClass.lean`, `Row1078.lean` and `Cover.lean` match the corresponding public files byte for byte. [Published matching optimizer](https://github.com/vjdad4m/maths/blob/1a203bc03c27b831ed6d3662cb05a572dbbe19dd/autographforge-1078/Row1078.lean) · [Published cover optimizer](https://github.com/vjdad4m/maths/blob/1a203bc03c27b831ed6d3662cb05a572dbbe19dd/autographforge-1125/Cover.lean)

With Lean 4.19.0 on PATH and a built Mathlib 4.19.0 checkout at `c44e0c8ee63ca166450922a373c7409c5d26b00b`, run in the extracted directory

```bash
MATHLIB_DIR=/absolute/path/to/mathlib4 bash replay.sh
```

The script rebuilds all twenty Lean modules with warnings as errors into a fresh temporary directory. It checks the axiom lists of seven result theorems. The expected lists contain only `propext`, `Classical.choice` and `Quot.sound`. For the numerical and release audit, install GraphCalc 2.0.0 and NetworkX 3.5 with a supported MILP solver, then supply the pinned upstream checkout including its archived graph6 blob.

```bash
python audit.py /absolute/path/to/AutoGraphForge
```

Expected outputs are saved in `Replay.log` and `SourceAudit.log`.
