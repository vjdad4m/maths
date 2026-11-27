# Power domination versus two-forcing on cographs

**AutoGraphForge physical row 188 is true.** Every finite simple cograph of order at least two satisfies $\gamma_P(G)\le F_2(G)$. Disconnected graphs and isolated vertices are included. On $K_{3,3}$ both parameters equal two, and $F_3=1$. Thus even on connected cographs, threshold three already fails in this inequality. [Row theorem](Row188.lean) · [Sharpness](Sharp.lean)

## The stronger theorem

Suppose every connected component with at least two vertices is a join of two nonempty graphs. All cross-edges between the two shores are present, and the graphs within the shores can be arbitrary. For every two-forcing set $S$ there is a power-dominating set $D$ such that, in every component $C$,
$$|D\cap C|\le \min\{2,|S\cap C|\}.$$
This includes, for example, a universal vertex joined to an induced four-vertex path, which lies outside the cographs. The theorem allows both arbitrary join factors and arbitrary disjoint unions. [Conversion theorem](Row188.lean) · [Join hypotheses and small-shore lemma](Components.lean)

Every successful two-forcing set contains a seed in each component. If a component contains at least two seeds, choose one vertex from each join shore. Their closed neighborhoods already cover the component. If the component contains only the seed $x$ and has other vertices, then $x$ must be able to make the first force. Its initially uncolored neighbors include the entire opposite shore, so that shore has size at most two. A vertex $y$ of that shore observes the opposite side immediately. At most one vertex remains unseen, and $x$ can force it. A singleton component keeps its sole seed. The cograph result follows because a nontrivial connected induced-$P_4$-free graph is a proper join.

In $K_{3,3}$ a single power seed leaves two vertices from its own shore unseen. These vertices have identical open neighborhoods, so neither can be forced first. One vertex from each side suffices for two-forcing. For three-forcing a single vertex forces the opposite shore in one round and the remaining vertices in the second. The Lean proof checks the inducing class, connectedness and all three numeric optima. [Fort lemma](TwinFort.lean) · [Checked example](Sharp.lean)

## Catalogue, implementations and attribution

Ján Pastorek's pinned row is marked `promising:class`, with 548 normalized touches. CEGIS record `ec83a5d2` has status `proposed`, 1,714 raw touches and no attached Lean proof. Rows 195, 197, 225 and 228 have extra hypotheses and are explicitly tagged `trivial:subsumed`. The release has no identically stated verified proof or direct refutation. Its public issue concerns a different ID. The shared index at `c2d4b8bc2db61524613cce96d2dcfe73b9521d0d` contains rows 383, 567 and 711 and has no entry for 188. [Pinned source line](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L188) · [CEGIS records](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/cegis_results.json) · [Shared index](https://github.com/vjdad4m/maths/blob/c2d4b8bc2db61524613cce96d2dcfe73b9521d0d/README.md) · [Upstream issue 1](https://github.com/JanPastorek/AutoGraphForge/issues/1)

GraphCalc 2.0.0 tests ordinary power domination by starting with the closed neighborhood and then applying the one-unobserved-neighbor rule. Its two-forcing process starts with the seeds alone and permits each colored vertex with at most two uncolored neighbors to color all those neighbors. The ordinary power minimum is modeled by the inductive observation relation. The two-forcing minimum uses GraphCalc's synchronous step iterated up to the graph order, when the increasing sets have stabilized. On the specified nonempty domain its search from one skips no successful set. GraphCalc recursively recognizes cographs via connected components of the graph or complement, inducing on the original graph. The shared row 143 proves the equivalence with the induced-path definition used here. [Forcing implementation](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/invariants/zero_forcing.py#L56-L278) · [Two-forcing wrapper](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/invariants/zero_forcing.py#L463-L488) · [Power domination implementation](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/invariants/zero_forcing.py#L1059-L1304) · [Cograph implementation](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/core/basics.py#L1126-L1191) · [Recognition theorem](https://github.com/vjdad4m/maths/blob/c2d4b8bc2db61524613cce96d2dcfe73b9521d0d/autographforge-cograph/CographRadius.lean)

The join decomposition of connected cographs, the domination of a join by one vertex from each shore, and the obstruction from identical open neighborhoods are standard ingredients. Yuliana, Dafik, Agustin and Wardani prove power-domination formulas for several join families. Ferrero, Hogben, Kenter and Young study relations between forcing and power domination with parameter $k$. Targeted searches for ordinary power domination versus two-forcing on cographs and joins located no earlier statement of this componentwise conversion. Priority remains unestablished. [Join formulas](https://doi.org/10.1088/1742-6596/1211/1/012020) · [Forcing and power domination](https://arxiv.org/abs/1701.08386) · [Smith and Hicks on fort neighborhoods](https://doi.org/10.1002/net.22056)

`Proof137` and `CographJoin` reproduce the shared Graffiti.pc 137 and row 143 structural proofs from the row 534 packet. `ForcingBasis` extracts the step, optimum and supporting lemmas from row 711. `PowerBasis` uses the ordinary observation model from row 66. `TwinFort` retains the checked twin-pair obstruction from rows 383/567. The biclique representation and Boolean shore argument follow the row 1883 module. [Structural basis](https://github.com/vjdad4m/maths/blob/c2d4b8bc2db61524613cce96d2dcfe73b9521d0d/autographforge-534/CographJoin.lean) · [Forcing basis](https://github.com/vjdad4m/maths/blob/c2d4b8bc2db61524613cce96d2dcfe73b9521d0d/autographforge-711/Row711.lean) · [Power basis](https://github.com/vjdad4m/maths/blob/c2d4b8bc2db61524613cce96d2dcfe73b9521d0d/autographforge-66/PowerBurning.lean) · [Twin-pair fort](https://github.com/vjdad4m/maths/blob/c2d4b8bc2db61524613cce96d2dcfe73b9521d0d/autographforge-book-forts/Forts.lean) · [Biclique source](https://github.com/vjdad4m/maths/blob/c2d4b8bc2db61524613cce96d2dcfe73b9521d0d/autographforge-balanced-forcing/BalancedForcing.lean)

## Verification

With Lean 4.19.0 on PATH and a built Mathlib 4.19.0 checkout at `c44e0c8ee63ca166450922a373c7409c5d26b00b`, run from the extracted source directory.

```bash
MATHLIB_DIR=/absolute/path/to/mathlib4 bash replay.sh
```

This compiles all eight source modules into a fresh object directory with warnings as errors and checks the six printed axiom lists. Each contains only `propext`, `Classical.choice` and `Quot.sound`. [Lean output](Replay.log)

The independent audit examines all 4,776 distinct graph6 encodings from the pinned backup and refutation files. All 1,334 qualifying encodings satisfy the inequality, including 643 disconnected graphs and 421 with isolates. It verifies a power seed in each component and tests all singletons for two-forcing whenever it needs a two-seed lower bound. The upstream invariant battery checks $K_{3,3}$, its union with two isolates, and the cone over $P_4$. With GraphCalc 2.0.0, NetworkX 3.5 and the pinned AutoGraphForge pipeline dependencies installed, run

```bash
python audit.py /absolute/path/to/AutoGraphForge
```

[Audit program](audit.py) · [Audit output](SourceAudit.log)
