# AutoGraphForge row 821 and the Slater number of forests

**Row 821 holds throughout GraphCalc’s numerical diameter domain.** For a finite simple graph of order at least two which is bipartite and chordal, every defined diameter satisfies $d\le 3s-1$, where $s$ is its Slater number. The nine-vertex path attains equality. In Ján Pastorek's normalized survivor file this is physical line 821, generated ID `961f5019`, with 92 touches. The pinned generated record is marked `proposed` with a null Lean proof. The exact statement did not appear in the three release refutation files, two verified proof files, public upstream issue, or shared checked index inspected on 27 November 2026. [Normalized row](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L821) · [Generated records](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/cegis_results.json) · [Release proofs](https://github.com/JanPastorek/AutoGraphForge/tree/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/verified_proofs) · [Upstream issue](https://github.com/JanPastorek/AutoGraphForge/issues/1) · [Checked maths index](https://github.com/vjdad4m/maths/blob/main/README.md)

## Prior result

Wyatt J. Desormeaux, Teresa W. Haynes and Michael A. Henning proved in 2014 that a tree of order $n\ge3$ with $L$ leaves satisfies $3s\ge n-L+2$. A diametral path of length $d$ has $d-1$ distinct internal vertices, so $n-L\ge d-1$. The connected row follows immediately, with $K_2$ settled directly. The formalization gives an independent proof of this known consequence. The all-forest path version also follows by joining components into a tree on the same vertices. Every original simple path is still a simple path, and adding edges can only decrease the Slater number. [Desormeaux, Haynes and Henning, *Improved bounds on the domination number of a tree*, Discrete Applied Mathematics 177 (2014), 88–94](https://doi.org/10.1016/j.dam.2014.05.037) · [Authors’ university record](https://dc.etsu.edu/etsu-works/15654/)

## Two diameter conventions

GraphCalc 2.0.0 uses ordinary chordality, bipartiteness and order at least two. It computes the Slater number as the least $t$ for which $t$ plus the sum of the $t$ highest degrees is at least the order. Its numerical diameter calls NetworkX, which raises an exception on disconnected nontrivial graphs. AutoGraphForge's CEGIS loop uses GraphCalc's invariant table with undefined entries masked. The Lean theorem `row821_graphcalc` takes a returned diameter as its hypothesis. [Graph classes and diameter](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/core/basics.py) · [Slater implementation](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/invariants/degree.py#L227-L365) · [Generation pipeline](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/pipeline/cegis.py#L1-L11) · [Missing-value handling](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/pipeline/invariants_graphcalc.py#L57-L76)

The separate AutoGraphForge wrapper uses positive infinity as its undefined-value sentinel. Treating that sentinel as a numerical value makes the unrestricted inequality false. Two isolated vertices are nontrivial, bipartite and chordal, with degree sequence $(0,0)$, $s=2$, and wrapper value $+\infty>5$. Lean certifies the class, exact Slater number and failed comparison. The source crosscheck runs both diameter implementations on this graph and the equality example $P_9$. [Wrapper](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/graphs/invariants.py#L269-L275)

## The checked argument

Write $E=\sum_v\max(\deg(v)-2,0)$ and $M=\sum_v\max(\deg(v)-1,0)$. Any $s$ degrees sum to at most $2s+E$, so the defining inequality for $s$ gives $n\le3s+E$. Each nonsingleton tree component of order $m$ contributes $m-2$ to $M$ by the degree-sum formula. A singleton contributes zero. Therefore $M+2\le n$ in any forest of order at least two.

For a simple path with $D\ge1$ edges, each of its $D-1$ internal vertices has two distinct path neighbors and contributes one unit to $M-E$. Combining the three inequalities gives $D+1\le3s$. The proof covers the zero-length path as well. Bipartite chordal graphs are forests, so this applies to a shortest path between any two vertices of a connected graph.

The proof uses the byte-for-byte local copy of the published row 370 module for its forest characterization. The descending-degree list and Slater definition come from row 33, and the finite diameter uses the iterated maximum of Mathlib graph distances from row 764. All degree sums, simple paths, component counts and the two-isolate calculation are proved in the local source. [Row 370](https://github.com/vjdad4m/maths/blob/main/autographforge-370/OuterForest.lean) · [Row 33](https://github.com/vjdad4m/maths/blob/main/autographforge-33/Lollipop.lean) · [Row 764](https://github.com/vjdad4m/maths/blob/main/autographforge-eulerian-chain/Chain.lean)

## Reproduce

The proof imports the adjacent published row-370 `OuterForest.lean` and rebuilds it from source. With Lean 4.19.0 on PATH and a prepared Mathlib v4.19.0 checkout at commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`, run from this directory:

```bash
MATHLIB_DIR=/absolute/path/to/mathlib4 bash replay.sh
```

The script rebuilds the local dependency in a temporary directory, checks both files with warnings as errors, and checks the exact axiom output for all six reported theorems. Each uses only `propext`, `Classical.choice` and `Quot.sound`.

For the independent implementation check, install GraphCalc 2.0.0 and NetworkX 3.5 and check out AutoGraphForge at `4d1a8afc99447cacd2328cca20e47b6493e8dbc5`. Run `python check_source.py /absolute/path/to/AutoGraphForge`.
