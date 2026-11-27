# AutoGraphForge normalized row 370

For every finite simple bipartite chordal graph of order at least two, the independence number is at most the outer-connected domination number whenever GraphCalc returns a number. Connectivity of the ambient graph is unnecessary. The proof establishes the stronger bound for every outer-connected dominating set in every finite forest.

## Proof

A shortest cycle of a bipartite graph cannot have length three. In a chordal graph a longer cycle has a chord, which cuts off a shorter cycle. Thus a bipartite chordal graph is a forest. The Lean definition of chordality quantifies over the edges and vertices of the actual cycle.

Let $D$ be an outer-connected dominating set and let $C=V-D$. Every vertex of $C$ has a neighbor in $D$. Two distinct vertices of $C$ cannot have a common neighbor in $D$, since their path in the connected induced graph on $C$ and the two-edge path through that neighbor would be distinct paths in a forest. Choose one such neighbor for each vertex of $C$. For an independent set $A$, this sends $A ∩ C$ injectively into $D-A$. Keeping each vertex of $A ∩ D$ fixed extends this to an injection from $A$ into $D$. Take a largest independent set and minimize over $D$.

## Source and attribution

Ján Pastorek's catalogue lists the statement on physical line 370, with 269 touches in the normalized table. The generated record is `1754b1ab`, with status `proposed` and null Lean proof. Its exact statement is absent from the three release refutation JSON files, the two release verified proof files, the public issue list and the checked maths index as inspected on 27 November 2026. The normalized audit labels it `promising:class`. [Pinned row](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L370) · [Generated records](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/cegis_results.json) · [Public issue](https://github.com/JanPastorek/AutoGraphForge/issues/1) · [Checked index snapshot](https://github.com/vjdad4m/maths/blob/84dc4a11b3c3e5d3730a10538e05f03ec2b07a5b/README.md)

Joanna Cyman used the same boundary-neighbor observation in the proof of Theorem 7, pp. 40–41, to show that an outer-connected dominating set of a tree has size at least half its order. Pairing vertices of an arbitrary independent set with their chosen neighbors gives the inequality here. Kulli and Janakiram studied the same parameter earlier under the name *nonsplit domination*. Searches under both names with independence, matching and tree bounds located no earlier statement of this exact inequality. These checks establish release status and identify prior proof content. They do not establish historical priority. [Cyman, Australasian Journal of Combinatorics 38 (2007), 35–46](https://ajc.maths.uq.edu.au/pdf/38/ajc_v38_p035.pdf) · [Kulli and Janakiram (2000)](https://www.researchgate.net/publication/266283658_The_nonsplit_domination_number_of_a_graph)

## Domain and reuse

GraphCalc 2.0.0 uses order at least two, NetworkX bipartiteness and ordinary chordality. Its independence routine maximizes the sum of the binary vertex variables subject to the edge exclusions. Its outer-connected routine enumerates nonempty sets by increasing size and requires their complement to induce a connected graph. Lean uses Mathlib's `indepNum`, proper two-colorings, walks, connectivity and path uniqueness in a forest. The published row 373 uses acyclicity and forcing, but its forcing theorems supply neither the domination predicate nor this matching. This file imports only Mathlib. [Graph classes](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/core/basics.py) · [Independent sets](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/invariants/classics.py#L46-L170) · [Outer-connected domination](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/invariants/domination.py#L629-L778) · [Published row 373](https://github.com/vjdad4m/maths/blob/84dc4a11b3c3e5d3730a10538e05f03ec2b07a5b/autographforge-373/AutoGraphForge373.lean)

On a nontrivial edgeless graph, domination requires all vertices and NetworkX raises `NetworkXPointlessConcept` on their empty complement. Lean represents this missing value by `none` and proves `outerNumber_defined_iff` for every finite simple graph. For an edge $xy$, removing $x$ from the full vertex set gives a feasible set. Conversely, a vertex of the nonempty complement and a neighbor dominating it give an edge. Through the public GraphCalc 2.0.0 API with NetworkX 3.5, the pairs (independence, outer-connected domination) were (1,1) on $K_2$, (3,3) on $P_5$, (4,4) on $K_{1,4}$, and (2,2) on an edge plus an isolate. Three isolates produced the stated exception.

## Replay

The full local proof source is `OuterForest.lean`. With Lean 4.19.0 on PATH and a prepared Mathlib 4.19.0 checkout at commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`, use the following command from this directory.

```bash
MATHLIB_DIR=/absolute/path/to/mathlib4 bash replay.sh
```

The script checks both pins, invokes `lake env lean -DwarningAsError=true` and checks the printed axioms for the final theorem and the three structural/domain theorems. The replay passed with exactly `propext`, `Classical.choice` and `Quot.sound` in each case. No supplementary Lean files or local object files are required.

