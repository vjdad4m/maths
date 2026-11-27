# Graffiti.pc #384b: the 33-count leaf-and-ear frontier

If a connected counterexample realizes exactly 33 distinct vertex triangle
counts, Lean reduces it to a connected graph on 33 vertices with one leaf,
one triangular ear, and 31 vertices of degree at least three. The leaf has
triangle count zero, the ear has count one, and they are nonadjacent. The
counts are pairwise distinct and the graph contains a five-clique. The final
graph is a spanning subgraph of an induced witness, not necessarily itself
induced in the original graph. All counts in the witness are preserved.

Two companion results are verified. Connected graphs realizing 33 counts
but missing the value one satisfy the catalogue inequality, regardless
of order. Also, deleting the zero-count vertex of a 33-vertex witness
leaves a connected positive core whose 2-domination number is exactly 16.
The reduction does not decide the remaining leaf-and-ear configuration
or the conjecture outside this diversity.

The combined theorem is `PositiveCore33.diversity33_frontier` in
`src/FrontierEar33.lean`. The proofs use the cut and parity arguments
from the [order-34 one-ear package](../graffiti-384b-one-ear/).

Use Lean 4.19.0 and Mathlib at `c44e0c8ee63ca166450922a373c7409c5d26b00b`:
```sh
CROSSFOUR_LEAN_BIN=/path/to/lean/bin CROSSFOUR_MATHLIB=/path/to/mathlib4 \
bash graffiti-384b-leaf-ear/replay.sh
```
