# AutoGraphForge row 1132. Clique cover and outer-connected domination

Every nontrivial subcubic tree has vertex clique cover number at most its outer-connected domination number. Lean proves this on the exact catalogue domain, including existence of the outer-connected optimum. The degree restriction can be dropped. More generally, for a finite connected simple graph with a numerical outer-connected optimum,

```text
θ(G) ≤ γ_oc(G) + β(G),       β(G) = |E(G)| − |V(G)| + 1.
```

Here θ is the minimum number of cliques partitioning the vertices, γ_oc is the minimum size of a dominating set whose complement induces a connected graph, and β is the cycle rank. For every integer β≥0 a connected bipartite graph attains equality. [Pastorek’s pinned normalized row 1132](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L1132)

## Proof

Fix an outer-connected dominating set D. Each vertex x outside D chooses a neighbor f(x) in D. For each chosen neighbor y keep just one pair (x,y). These pairs form a matching. Cover every retained pair by its edge, every unused vertex of D by a singleton, and each remaining outside vertex by its own singleton. Writing X for the outside vertices whose pair was discarded, the cover has |D|+|X| parts.

Delete the |X| discarded edges. The graph stays connected. To replace a deleted edge xy, travel from x within the connected complement of D to the outside vertex whose pair with y was kept, then take that retained edge to y. The remaining graph has at least |V|−1 edges, so |X|≤β(G). Minimizing over D proves the inequality. Trees have β=0. Lean works with the equivalent additive inequality to avoid truncated natural subtraction.

For sharpness at rank m, take the complete bipartite graph with sides of sizes m+2 and 2, and delete one edge. This leaves m+4 vertices and 2m+3 edges. The two endpoints of the missing edge form a dominating set whose complement is a star. The independent side of size m+2 forces at least m+2 clique labels. The bound then gives both exact optima, γ_oc=2 and θ=m+2. The Lean theorem `Sharp.sharp_family` verifies connectivity, the counts and both optima for every m≥0.

## Prior work and reuse

Joanna Cyman’s proof of Theorem 7 uses the fact that in a tree a vertex of D cannot have two neighbors in its connected complement. That observation already gives the tree result by pairing every outside vertex with a distinct neighbor in D. The shared row 370 formalization uses this pairing for the independence number, and row 1121 formalizes how a matching yields a vertex clique cover. The tree row is an application of this earlier argument. The cycle-rank proof permits repeated choices, counts them, and proves that its coefficient is sharp. Targeted literature searches under *outer-connected domination* and *nonsplit domination* located no earlier statement of this exact correction. Historical priority remains unverified. [Cyman, *The outer-connected domination number of a graph*, pp. 40–41](https://ajc.maths.uq.edu.au/pdf/38/ajc_v38_p035.pdf) · [Row 370](https://github.com/vjdad4m/maths/blob/790acdd3e04b4ce1ba602da3fd9619ac2e880463/autographforge-370/OuterForest.lean) · [Row 1121](https://github.com/vjdad4m/maths/blob/790acdd3e04b4ce1ba602da3fd9619ac2e880463/autographforge-1121/HallRainbow.lean)

The bundled dependencies are byte-identical to these public files at the indicated revision. `Row1132.lean` uses `OuterDominating`, `outerNumber`, `outerNumber_defined_iff`, `vertexCliqueCover` and `cover_of_matching`. Its graph argument uses Mathlib’s connected edge lower bound after deleting the repeated choices. The forcing dynamics from row 711 play no role in these invariants.

## Catalogue and software

At AutoGraphForge revision `4d1a8afc99447cacd2328cca20e47b6493e8dbc5`, normalized physical line 1132 has 58 touches and the CEGIS record `579ec124` has status `proposed`, 875 metadata touches, and empty Lean fields. Line 5385, record `9f880402`, says that a graph with γ_oc<θ cannot be a tree. It omits the degree bound. The theorem `row5385` checks the implication wherever the source invariants are numerical. Both records were absent from the three refutation JSON files and the released verified proofs. The sole upstream issue concerns another record. The inspected maths index at `790acdd3e04b4ce1ba602da3fd9619ac2e880463` includes 370 and 1121 and has no entry for 1132 or 5385. [Source records](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/cegis_results.json) · [Related line 5385](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L5385) · [Public issue](https://github.com/JanPastorek/AutoGraphForge/issues/1) · [Inspected index](https://github.com/vjdad4m/maths/blob/790acdd3e04b4ce1ba602da3fd9619ac2e880463/README.md)

GraphCalc 2.0.0 uses order at least two, maximum degree at most three, and the NetworkX tree predicate. It finds a minimum proper coloring of the complement graph and counts its nonempty color classes for θ. It searches for an outer-connected dominating set in increasing cardinality and tests connectivity on its induced complement. The latter test can raise on the empty complement. Row 370’s option-valued minimum represents absence of a numerical value. Every nontrivial tree has an edge and therefore a proper feasible set. [Graph classes](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/core/basics.py) · [Clique cover](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/invariants/classics.py#L428-L504) · [Outer-connected domination](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/invariants/domination.py#L629-L778)

The frozen audit screened all 4,776 distinct released graph6 encodings. Of 179 nontrivial trees, 76 qualified for row 1132, including 13 encodings appearing in the refutation files for other records. Both GraphCalc optimizers were recomputed on all 30 qualifying encodings of order at most eight. The upstream public battery gave (θ,γ_oc)=(3,3) on the five-vertex path and the three-leaf star, and (m+2,2) on the equality examples for m=0,1,2,3. The universal result comes from the Lean proof. [Public battery](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/pipeline/invariants_graphcalc.py#L125-L160)

## Strict replay

From the extracted source directory, use Lean 4.19.0 on PATH and a built Mathlib 4.19.0 checkout at commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`.

```bash
MATHLIB_DIR=/absolute/path/to/mathlib4 bash replay.sh
```

The corresponding command from this directory in the shared workspace is

```bash
PATH="$PWD/../outer-forest/.deps/lean-4.19.0-linux/bin:$PATH" \
MATHLIB_DIR="$PWD/../../graff169-180-codex/.work/mathlib" bash replay.sh
```

The script compiles both bundled dependencies, the general proof and the sharp family into a fresh object directory with warnings as errors. It checks all six printed result axiom lists, each containing only `propext`, `Classical.choice` and `Quot.sound`. The optional release audit requires GraphCalc 2.0.0, NetworkX 3.5 and the pinned AutoGraphForge checkout.

```bash
python audit.py /absolute/path/to/AutoGraphForge
```

