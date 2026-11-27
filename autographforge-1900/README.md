# AutoGraphForge row 1900. Outer-connected domination and maximum degree

For a finite simple Eulerian triangle-free graph of order at least two, its outer-connected domination number γₒ꜀ and its vertex clique cover number θ satisfy **γₒ꜀ ≤ 2θ − 2**. Equality holds precisely when the graph is 2-regular and admits a perfect matching. On the connected catalogue domain these graphs are the even cycles. The Lean criterion is phrased directly in terms of degrees and Mathlib perfect matchings. The square attains equality, with both optima equal to two. [Pastorek’s pinned physical line 1900](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L1900)

## A stronger bound

In every nonempty finite triangle-free simple graph of minimum degree at least two,

```text
γₒ꜀(G) + Δ(G) ≤ |V(G)|.
```

Here Δ denotes maximum degree. Connectivity of the ambient graph is unnecessary. Choose a vertex v of degree Δ and reserve one neighbor w. Put v and its other Δ−1 neighbors outside the dominating set D. These Δ vertices induce a connected star. The reserved w dominates v. Every other vertex x of the star has a neighbor besides v, and that neighbor lies outside the star because a triangle through v and x is forbidden. Thus D is an outer-connected dominating set of size |V|−Δ. The local Lean lemma needs independence only in the chosen center’s neighborhood and the degree-two lower bound only at its neighbors.

For every d≥2, the complete bipartite graph K₂,ᵈ has maximum degree d, order d+2, and outer-connected domination number two. It attains the stronger bound at every maximum degree. Its minimum degree stays two, so the improvement over the order-minus-minimum-degree estimate can grow without bound. Lean verifies this family, both optima for K₂,ᵈ, and the exact row assumptions for the square. [Family proof](Sharp.lean)

## The printed inequality and equality cases

A connected nontrivial Eulerian graph has even positive degrees and therefore minimum degree at least two. Every clique in a triangle-free graph has at most two vertices, so |V|≤2θ. With the star bound this gives γₒ꜀+2≤γₒ꜀+Δ≤|V|≤2θ.

If γₒ꜀+2=2θ, all three inequalities are equalities. Every degree is two and a minimum clique cover partitions the graph into pairs of adjacent vertices, giving a perfect matching. Conversely, if all degrees are two, every vertex outside an outer-connected dominating set has at most one neighbor also outside. A connected graph of maximum degree one has at most two vertices. Thus γₒ꜀≥|V|−2. A perfect matching partitions the vertices into cliques of size two. These observations give equality. The formal result also covers disconnected triangle-free graphs of minimum degree at least two.

## Earlier work and repository reuse

Joanna Cyman’s Theorem 5 gives γₒ꜀≤|V|−δ on connected graphs, where δ is the minimum degree. Combining that published result with δ≥2 and the size bound on triangle-free cliques already proves the printed row. Observation 1(ii, iv) gives the outer-connected domination formulas for cycles and complete multipartite graphs used for the examples. The work here gives the local star construction, its maximum-degree consequence, and a kernel-checked equality characterization. Targeted searches under *outer-connected domination* and *nonsplit domination* located no earlier statement of this specific maximum-degree refinement or catalogue equality criterion. Historical priority is unverified. [Cyman, *The outer-connected domination number of a graph*, Australas. J. Combin. 38 (2007), 35–46](https://ajc.maths.uq.edu.au/pdf/38/ajc_v38_p035.pdf)

Four bundled dependencies match the public source byte for byte at maths revision `f061743d92d401daca0c141ff95156895c01b20a`. Row 370 supplies the proper connected-complement predicate and its option-valued minimum. Row 1160 supplies the complement-coloring minimum, triangle-free color-class bound and both perfect-matching implications. Row 1121 supplies the complete-bipartite degree and clique-cover formulas used in the sharpness proof. `DegreeTwo.lean` extracts the public cycle proof’s general complement-size lemma, substituting the equivalent row 370 predicate. The row 1132 cycle-rank estimate bounds θ from above and does not prove this estimate for γₒ꜀. [OuterForest](https://github.com/vjdad4m/maths/blob/f061743d92d401daca0c141ff95156895c01b20a/autographforge-370/OuterForest.lean) · [Criterion](https://github.com/vjdad4m/maths/blob/f061743d92d401daca0c141ff95156895c01b20a/autographforge-1160/Criterion.lean) · [Biclique formulas](https://github.com/vjdad4m/maths/blob/f061743d92d401daca0c141ff95156895c01b20a/autographforge-1121/Boundary.lean) · [General degree-two lemma](https://github.com/vjdad4m/maths/blob/f061743d92d401daca0c141ff95156895c01b20a/autographforge-1130/CycleDomination.lean#L77-L116)

## Source conventions and release status

Ján Pastorek’s pinned AutoGraphForge revision is `4d1a8afc99447cacd2328cca20e47b6493e8dbc5`. Physical line 1900 has normalized touch count 20. Its CEGIS record `044250a9` has status `proposed`, 311 metadata touches, and empty Lean fields. The ID and statement were absent from the released verified proofs and the three refutation JSON files. The sole upstream issue concerned a different record. The inspected shared index had no line 1900 entry. Neighboring 1880 drops Eulerianity and changes the offset to −1; 2198 uses a different forbidden clique and coefficient. [Source records](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/cegis_results.json) · [Inspected index](https://github.com/vjdad4m/maths/blob/f061743d92d401daca0c141ff95156895c01b20a/README.md) · [Upstream issue](https://github.com/JanPastorek/AutoGraphForge/issues/1)

GraphCalc 2.0.0 requires order at least two for nontriviality, connectedness and all-even degrees for Eulerianity in the undirected domain, and absence of triangles. Vertex clique cover minimizes the number of nonempty color classes of a proper complement coloring. Outer-connected domination minimizes the size of a dominating set whose complement induces a connected graph. The star construction produces a proper feasible set, so `row1900` proves existence of the numerical optimum and uses signed integers for the displayed affine comparison. [Graph classes](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/core/basics.py) · [Clique cover](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/invariants/classics.py#L428-L504) · [Outer-connected domination](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/invariants/domination.py#L629-L778)

The audit screened 4,776 distinct released graph6 encodings. It checked a star-complement certificate on each of the 327 qualifying graphs, including 69 encodings used as witnesses for other records. For all 52 qualifying graphs of order at most ten, the audit recomputed both optima and the perfect-matching equality test. The upstream public battery returned (θ,γₒ꜀) equal to (2,2), (3,3), (3,4), (4,2), and (6,2) on C₄, C₅, C₆, K₂,₄ and K₂,₆, respectively. [Upstream public battery](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/pipeline/invariants_graphcalc.py#L125-L160)

## Strict replay

With Lean 4.19.0 on PATH, run from the extracted source directory using a built Mathlib 4.19.0 checkout at commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`.

```bash
MATHLIB_DIR=/absolute/path/to/mathlib4 bash replay.sh
```

The equivalent shared-workspace invocation from this directory is

```bash
PATH="$PWD/../outer-forest/.deps/lean-4.19.0-linux/bin:$PATH" \
MATHLIB_DIR="$PWD/../../graff169-180-codex/.work/mathlib" bash replay.sh
```

The script builds every source dependency in a fresh directory with warnings as errors. It checks that the seven result theorems print only `propext`, `Classical.choice`, and `Quot.sound`. The optional numerical audit uses GraphCalc 2.0.0, NetworkX 3.5 and the pinned AutoGraphForge checkout.

```bash
python audit.py /absolute/path/to/AutoGraphForge
```
