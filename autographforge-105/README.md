# Hereditary equality of domination and power domination

**AutoGraphForge physical row 105 is true.** On a finite chordal cograph, the domination number and the ordinary power domination number both equal the number of connected components, counting isolated vertices. This applies to every induced subgraph. The catalogue asks for the first number to be at most the second on graphs of order at least two. [Pinned row 105](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L105) · [Row proof](Structure.lean) · [Result on induced vertex sets](Hereditary.lean)

**The converse holds hereditarily.** A finite graph is chordal and a cograph if and only if every induced subgraph has equal domination and power domination numbers. It suffices to test the catalogue inequality on four-vertex induced subgraphs. Either minimal obstruction, the path $P_4$ or the cycle $C_4$, gives domination number 2 and power domination number 1. Equality on the graph itself can occur outside the class. The cone over $P_4$, for example, has a universal vertex and contains an induced $P_4$. [Four-vertex test and exact obstruction values](Hereditary.lean)

## Proof

The structural class is the classical class of trivially perfect graphs. A connected nontrivial cograph has a partition into two nonempty sets with every cross-edge present. If each set contained two nonadjacent vertices, those four vertices would induce a square. Hence in a square-free join one shore is a clique, and each vertex of that shore is universal. Applying this to each component supplies one universal center per component. [Join and component lemmas](Structure.lean) · [Golumbic, *Trivially perfect graphs* (1978)](https://doi.org/10.1016/0012-365X(78)90178-4)

The centers constitute a dominating set. Every dominating set is power-dominating, since it observes the entire graph in the initial round. Conversely, every power-dominating set must meet every component. Induction on observation shows that each observed vertex lies in the component of some seed. The two optima are therefore equal to the number of components. The argument treats singleton components in the same count. [Optimization and component counts](Counts.lean)

For the reverse implication, an induced cycle of length at least five contains an induced path on four consecutive vertices. Both four-vertex obstructions need at least two ordinary dominators because neither has a universal vertex. In the labeling $0,1,2,3$ along the path or cycle, the pair $1,2$ dominates while the single power seed 1 initially observes $0,1,2$ and then vertex 2 can force vertex 3. Thus the four-vertex test excludes $P_4$ and every induced cycle of length at least four. The theorem `four_vertex_test` is stated using injections from `Fin 4`. The theorem `on_induced` gives both invariant values directly on Mathlib’s `G.induce s` for any vertex set of a finite graph.

## Scope, attribution and implementation

Ján Pastorek’s CEGIS record `516f48da` is marked `proposed` at revision `4d1a8afc99447cacd2328cca20e47b6493e8dbc5`. It has 888 normalized touches, 1,399 raw touches and no attached Lean proof. The exact claim is absent from the three release refutation reports and bundled verified proofs. The upstream public issue concerns a different record. The shared index at `c2d4b8bc2db61524613cce96d2dcfe73b9521d0d` has no row 105 entry. [CEGIS records](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/cegis_results.json) · [Public issue](https://github.com/JanPastorek/AutoGraphForge/issues/1) · [Shared index](https://github.com/vjdad4m/maths/blob/c2d4b8bc2db61524613cce96d2dcfe73b9521d0d/README.md)

The row is an elementary consequence of the classical trivially perfect graph characterization and the standard rules of power domination. The hereditary equality and four-vertex test combine that structure with the explicit computations for the two forbidden graphs. Searches for prior statements using “power domination perfect,” hereditary equality of domination and power domination, and power domination on trivially perfect graphs did not locate this exact invariant characterization. Its mathematical priority remains unestablished. [Golumbic’s original paper](https://doi.org/10.1016/0012-365X(78)90178-4) · [Haynes, Hedetniemi, Hedetniemi and Henning on power domination](https://doi.org/10.1137/S0895480100375831)

GraphCalc 2.0.0 uses closed neighborhoods for ordinary domination. Power domination starts with the closed neighborhoods of all seeds, followed by the unique-unobserved-neighbor forcing rule. The implementation starts its minimum search at one. On the empty graph it returns `None` for power domination. The catalogue requires order at least two. The hereditary Lean extension uses the mathematical empty-graph value zero for both minima. GraphCalc tests cographs recursively by graph or complement components, and tests chordality via NetworkX. [Domination implementation](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/invariants/domination.py#L43-L186) · [Power domination implementation](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/invariants/zero_forcing.py#L1059-L1302) · [Class tests](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/core/basics.py)

`Proof137` and `CographJoin` retain the checked Graffiti.pc 137 and row 143 join machinery from the row 534/188 files. `PowerBasis` uses the row 66 inductive observation relation. `ChordalBasis` extracts the forbidden-induced-cycle predicates from row 1915. The ordinary domination model in `Counts` follows the row 1078 closed-neighborhood predicate and row 574 optimizer. [Cograph join proof](https://github.com/vjdad4m/maths/blob/c2d4b8bc2db61524613cce96d2dcfe73b9521d0d/autographforge-534/CographJoin.lean) · [Row 143 recognition proof](https://github.com/vjdad4m/maths/blob/c2d4b8bc2db61524613cce96d2dcfe73b9521d0d/autographforge-cograph/CographRadius.lean) · [Row 66 power domination](https://github.com/vjdad4m/maths/blob/c2d4b8bc2db61524613cce96d2dcfe73b9521d0d/autographforge-66/PowerBurning.lean) · [Chordality](https://github.com/vjdad4m/maths/blob/c2d4b8bc2db61524613cce96d2dcfe73b9521d0d/autographforge-1915/TriangleChain.lean) · [Domination optimum](https://github.com/vjdad4m/maths/blob/c2d4b8bc2db61524613cce96d2dcfe73b9521d0d/autographforge-574/Bound.lean)

## Reproduction

With Lean 4.19.0 on PATH and Mathlib 4.19.0 built at `c44e0c8ee63ca166450922a373c7409c5d26b00b`, run in the extracted source directory.

```bash
MATHLIB_DIR=/absolute/path/to/mathlib4 bash replay.sh
```

Seven source modules compile into an empty temporary object directory with warnings as errors. The script checks all seven named axiom lists against `propext`, `Classical.choice` and `Quot.sound`. [Lean output](Replay.log)

For the source and graph6 audit, install GraphCalc 2.0.0, NetworkX 3.5 and the pinned AutoGraphForge pipeline dependencies, then run

```bash
python audit.py /absolute/path/to/AutoGraphForge
```

The audit checks all 4,776 distinct released encodings. Each of the 912 qualifying graphs has a dominating and power-dominating set with one universal center per component. Of these, 559 are disconnected and 370 have isolates. GraphCalc's public battery also checks $P_4$, $C_4$, the claw with two isolated vertices, and the cone over $P_4$. [Audit script](audit.py) · [Audit output](SourceAudit.log)
