# Graffiti.pc #384b: closing the order-34 one-ear case

Lean proves that every connected counterexample on more than two vertices
would contain a connected induced counterexample on **at most 33 vertices**
with exactly the same set of local triangle counts. At diversity 33 that
witness must have exactly 33 vertices, pairwise distinct counts, a five-clique,
and a vertex of degree at most two that lies in no triangle. This is a
reduction, not a resolution of the conjecture.

The main new argument handles a degree-two vertex whose two neighbors are
adjacent. Delete the three edges of that triangle. If the two neighbors
separate, orient their components' cuts independently. If they stay connected,
use a supporting triangle to repair the parity of an odd path between them.
The resulting even cycle through the degree-two vertex can be colored
alternately and extended to the needed cut.

See `Graffiti384b.OneEar.induced_bound`, `diversity33_failure` and the
order-34 theorem `at_most_seventeen` in `src/OneEarFinish384b.lean`.
The package extends the [two-ear proof](../graffiti-384b-two-ears/) and uses
its published frozen dependencies. Use Lean 4.19.0 and Mathlib at
`c44e0c8ee63ca166450922a373c7409c5d26b00b`:

```sh
CROSSFOUR_LEAN_BIN=/path/to/lean/bin CROSSFOUR_MATHLIB=/path/to/mathlib4 \
bash graffiti-384b-one-ear/replay.sh
```
