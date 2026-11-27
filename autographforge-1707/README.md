# AutoGraphForge normalized row 1707

**Disproved.** A connected claw-free graph of order 14 has minimum vertex clique-partition number 4 and singleton three-rainbow domination number 3. There is an infinite family with the rainbow number fixed at 3 and every clique-partition number from 2 upward. [Pinned row](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L1707)

## Witness and proof

Start with the triangle-free four-chromatic Grötzsch graph H, the Mycielskian of the five-cycle. Add three isolated vertices to H, then complement the result to obtain G. The three new vertices are universal in G. Give them one color each. Every uncolored vertex sees all three colors. Any feasible labeling on at least three vertices needs at least three colored vertices: either all vertices are colored, or an uncolored vertex sees three distinct colored neighbors. Thus the singleton rainbow number is exactly 3. The complement is triangle-free, so there cannot be three pairwise nonadjacent leaves of a claw in G. A universal vertex makes G connected.

The clique parts of G are the color classes of its complement. Restricting a complement coloring to H gives a coloring of H, and the three isolates can use an existing color. Thus the vertex clique-partition number is exactly the chromatic number of H.

Lean proves the Mycielski construction used here for arbitrary finite stages. Starting at K₂, replace each vertex by an old vertex and a shadow, retain the old edges, join each shadow to the old neighbors of its original, and join a new apex to all shadows. Triangle-freeness persists. A k-coloring extends to a (k+1)-coloring by copying each old color to its shadow and giving the apex a new color. Conversely, in any coloring, recolor each old vertex having the apex color with its shadow's color. Two adjacent old vertices cannot both be recolored, each shadow sees every old neighbor of its original, and all shadows avoid the apex color. The restriction therefore uses one fewer color. These are Jan Mycielski's classical construction and proof. Applying the complement construction at stage n yields order 3·2ⁿ+2, clique-partition number n+2 and singleton rainbow number 3. The explicit counterexample is stage 2. [Mycielski, *Sur le coloriage des graphs*, Colloquium Mathematicum 3 (1955), 161–162](https://doi.org/10.4064/cm-3-2-161-162)

## Source and status

Ján Pastorek's normalized physical row 1707 has generated ID `ae818342`, label `promising:class` and 30 normalized touches. At pin `4d1a8afc99447cacd2328cca20e47b6493e8dbc5` the record is proposed with null Lean proof. The source audit checks the physical line, generated record, uniqueness in the normalized list, released verified proofs and three refutation files. The public maths index at `1d67dcd7e82387c47debd06cd74ca913cbd9a2da` had no row 1707 result. The upstream issue concerned ID `f0a6258d`. I found no prior disproof of this exact singleton inequality in those sources or targeted searches on clique cover and singleton rainbow domination in claw-free graphs. The claimed application is to the specified catalogue row. [Upstream records](https://github.com/JanPastorek/AutoGraphForge/tree/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results) · [Checked public index](https://github.com/vjdad4m/maths/blob/1d67dcd7e82387c47debd06cd74ca913cbd9a2da/README.md) · [Upstream issue](https://github.com/JanPastorek/AutoGraphForge/issues/1)

The Lean definitions reproduce the singleton palette, cost and claw predicate from row 720, and the complement-color definition of clique partition from row 621. GraphCalc permits at most one color per vertex and optimizes the number of colored vertices. For clique partitions, it minimizes the number of colors on the complement. [GraphCalc rainbow optimizer](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/invariants/domination.py#L1159-L1201) · [Three-color entry point](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/invariants/domination.py#L1306-L1337) · [Clique partition](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/invariants/classics.py#L427-L504) · [Claw predicate](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/core/basics.py#L836-L877)

All 105 eligible graphs among the 312 released graph6 witnesses satisfy this row. The audit checks a valid clique partition of each connected component against lower bounds for its rainbow number. Vertices of degree less than three must be colored. If b vertices are colored in a component of order n and maximum degree D, then 3(n−b) ≤ Db by counting edges from uncolored to colored vertices. In a nontrivial claw-free component the bound from row 720 also gives at least one more than the size of any exhibited independent set. Both parameters are additive over components. Finally the audit constructs the order-14 witness and solves both GraphCalc optimizers.

## Replay

Use Lean 4.19.0 on PATH and a prepared Mathlib v4.19.0 checkout at `c44e0c8ee63ca166450922a373c7409c5d26b00b`. From the extracted directory run

```bash
MATHLIB_DIR=/absolute/path/to/mathlib4 bash replay.sh
```

The single Lean module imports Mathlib. The replay turns warnings into errors and checks the axiom lists for the core family, clique and rainbow values, separation theorem, order-14 witness and final disproof. Each uses exactly `propext`, `Classical.choice` and `Quot.sound`.

The independent audit requires GraphCalc 2.0.0, NetworkX 3.5, PuLP with a supported solver, and the pinned AutoGraphForge checkout.

```bash
python check_source.py /absolute/path/to/pinned/AutoGraphForge
```
