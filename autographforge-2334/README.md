# AutoGraphForge row 2334

A 14-vertex tree refutes the proposed bound on outer-connected domination for nontrivial chordal subcubic graphs. Both parameters are defined on the witness.

## Counterexample

Join vertices 0 and 1. Give 0 two children, 2 and 3, and give 1 two children, 4 and 5. Give each of 2, 3, 4 and 5 two leaf children, labeled 6 through 13 in that order. The resulting tree is connected, has maximum degree three and has no cycles, so it is chordal.

The eight leaves and vertex 0 form an independent set. By the forest bound proved for row 370, any outer-connected dominating set has at least nine vertices. Every vertex is within two edges of one of the two adjacent central vertices. Thus any two vertices are at distance at most five. Summing the three pairwise distances gives triameter at most fifteen. The right side of row 2334 is at most $15/2+1=8.5$, strictly less than nine.

The checked theorem uses those two bounds. Independently, GraphCalc 2.0.0 returned independence number 9, triameter 14 and outer-connected domination number 10 on the same labeled graph. Its numerical result gives $10>14/2+1=8$.

## Catalogue and conventions

The physical line is 2334, the normalized touch count is 6, and the generated ID is `37af8e28`. The pinned release lists the statement as `proposed` with null Lean proof and classifies it as `promising:class`. Its hypotheses are order at least two, chordal and subcubic. Connectivity is needed by the triameter routine and is proved for the witness. The source uses ordinary rational one-half. [Pinned row](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L2334) · [Generated records](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/cegis_results.json)

GraphCalc takes the maximum over unordered triples of distinct vertices of the sum of three shortest-path distances. Lean takes the maximum over ordered triples of distinct vertices, which gives the same maximum by symmetry. Both give zero when no triple exists. The outer-connected domination number minimizes the size of a dominating set whose complement induces a connected graph. Every actual edge ensures a feasible set. [Triameter](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/invariants/classics.py#L780-L818) · [Domination](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/invariants/domination.py#L629-L778) · [Graph classes](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/core/basics.py#L663-L791)

## Attribution and scope

Ján Pastorek's AutoGraphForge generated the proposed inequality. The checked forest domination bound from row 370 supplies the lower bound. The triameter definition comes from the checked row 764 certificate. Its proof uses the boundary observation of Joanna Cyman, Theorem 7, pp. 40–41. Hak, Kozerenko and Oliynyk studied triametral triples and bounds for trees. Before preparing this certificate, the exact generated statement was absent from the three release refutation records and the two release verified proofs. The public upstream issue concerned row 2596. The checked maths index and targeted searches on the conjecture, tree triameter, outer-connected domination and nonsplit domination did not identify an earlier resolution of this particular row. [Row 370 proof](https://github.com/vjdad4m/maths/blob/main/autographforge-370/OuterForest.lean) · [Row 764 definition](https://github.com/vjdad4m/maths/blob/main/autographforge-eulerian-chain/Chain.lean) · [Cyman (2007)](https://ajc.maths.uq.edu.au/pdf/38/ajc_v38_p035.pdf) · [Hak, Kozerenko and Oliynyk](https://doi.org/10.1016/j.dam.2021.12.011) · [Upstream issue](https://github.com/JanPastorek/AutoGraphForge/issues/1)

## Replay

With Lean 4.19.0 on PATH and a prepared Mathlib checkout at `c44e0c8ee63ca166450922a373c7409c5d26b00b`, run the following from this folder.

```bash
MATHLIB_DIR=/absolute/path/to/mathlib4 bash replay.sh
```

The only local Lean sources are `OuterForest.lean` and `BranchedTree.lean`. The former is a byte-for-byte copy of the checked row 370 source. The script rebuilds it in a temporary directory before checking the counterexample with warnings as errors.

