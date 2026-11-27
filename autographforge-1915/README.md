# AutoGraphForge row 1915

**Row 1915 is false, with an unbounded gap even at maximum degree four.** Five triangles joined end to end at single vertices give a connected chordal Eulerian graph of order 11. Its Slater number is 3 and its maximum degree is 4. The proposed inequality evaluates to $6\le4$.

The conjecture is Ján Pastorek’s normalized physical line 1915 at commit `4d1a8afc99447cacd2328cca20e47b6493e8dbc5`. The generated record `0a07813a` has 19 touches, status `proposed`, and a null Lean proof. Its hypotheses are nontriviality, chordality and the Eulerian property. The conclusion is $2s(G)\le\Delta(G)$. The normalized file on the default branch had the same blob `11d0dd0f999791efeab05b043d805fcf3bd33e99` when checked on 27 November 2026. All three release refutation files lacked the exact statement. The two released verified proofs concern clique number versus order and minimum versus maximum degree. The public issues and the shared maths README contained no solution for row 1915 when checked. [Pinned row](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L1915) · [Released results](https://github.com/JanPastorek/AutoGraphForge/tree/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results) · [Public issue](https://github.com/JanPastorek/AutoGraphForge/issues/1) · [Checked index](https://github.com/vjdad4m/maths/blob/main/README.md)

## Proof

For $t\ge1$ take vertices $0,\dots,2t$ and put a triangle on each triple $2i,2i+1,2i+2$ for $0\le i<t$. The edges between successive labels give connectivity. Each shared vertex has degree four and each remaining vertex has degree two. Thus the graph is Eulerian. At each label its lower-labeled neighbors form a clique. The largest label on a hypothetical induced cycle of length at least four would give a chord, proving chordality.

For $t=5$ the four shared vertices have degree four and the other seven vertices have degree two. The Slater number is the least $s$ such that the $s$ largest degrees, plus $s$, reach the order. Even the two largest degrees give only $2+4+4=10$, whereas three give $3+4+4+4=15$. Hence $s=3$.

More generally, at most $s\Delta$ can come from the first $s$ degrees, so $n\le(\Delta+1)s$. For $t\ge2$ the chain has $\Delta=4$ and $n=2t+1$. All $t\ge5$ therefore violate the row. The theorem `unbounded_gap` proves that for each natural $g$ a nontrivial chordal Eulerian chain satisfies $\Delta=4$ and $\Delta+g<2s$. The Lean parameter `m` denotes $t-1$.

## Prior work, reuse and source conventions

The graph family is the classical chain triangular cactus. Alikhani, Jahari and Mehryar studied this same family and its domination polynomials. The lower bound $s\ge\lceil n/(\Delta+1)\rceil$ also appears in work of Desormeaux, Haynes and Henning. Together the established family and degree estimate directly imply the failure of this catalogue proposal. The local file supplies the exact witness and a formal family proof. A targeted check found no earlier row-specific resolution. [Alikhani, Jahari and Mehryar, *On the domination polynomials of cactus chains*](https://arxiv.org/abs/1403.1999) · [Desormeaux, Haynes and Henning, *Improved bounds on the domination number of a tree*](https://doi.org/10.1016/j.dam.2014.05.037)

The proof reuses the forbidden-induced-cycle definition, elimination-order lemma, Euler criterion and sorted-degree Slater definition from the published #501/#764 module. Its particular five-clique witness has $s=2$ and $\Delta=6$, satisfying row 1915. Here all the blocks are triangles. The new source proves the family’s neighborhood and degree formulas for arbitrary length and uses Mathlib’s `SimpleGraph.maxDegree`. [Published chain certificate](https://github.com/vjdad4m/maths/blob/main/autographforge-eulerian-chain/Chain.lean) · [Published Slater definition from #33](https://github.com/vjdad4m/maths/blob/main/autographforge-33/Lollipop.lean)

GraphCalc 2.0.0 defines nontriviality by order at least two, uses NetworkX for chordality and the undirected Eulerian test, computes the maximum of the degree sequence, and computes the Slater number from its decreasing order. Every witness here is connected and all five source quantities are defined. The independent Python check constructs the graphs by adding the three edges of each triangle, then calls these public GraphCalc entry points. [GraphCalc class tests](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/core/basics.py) · [GraphCalc degree invariants](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/invariants/degree.py#L151-L363)

## Replay

The complete local Lean source is `TriangleChain.lean`. With Lean 4.19.0 on PATH and a prepared Mathlib v4.19.0 checkout at commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`, run from this directory:

```bash
MATHLIB_DIR=/absolute/path/to/mathlib4 bash replay.sh
```

The script promotes warnings to errors and checks the axiom output for all seven audited theorems. Their only axioms are `propext`, `Classical.choice` and `Quot.sound`. With GraphCalc 2.0.0 and NetworkX 3.5 installed, run `python check_source.py /absolute/path/to/pinned/AutoGraphForge` to repeat the independent source check for 1 through 24 triangles.
