# Graffiti.pc #189: the degree-four case through eleven vertices

**Partial result.** Lean proves the Hamiltonian-path conclusion for a two-connected graph on at most eleven vertices when at most one vertex has degree below four and every vertex has at most five vertices at even distance, including itself.

The proof is structural. It counts the positions used by endpoint adjacencies on a longest path and uses rotations to exclude two additional positions if a vertex was omitted. See [SmallOrderFour189.lean](src/SmallOrderFour189.lean), theorem `traceable_of_order_le_eleven`. This does not settle larger orders or the general conjecture.

In a Lean and Mathlib 4.19.0 project, run `lake env bash /path/to/maths/graffiti-189-order-eleven/replay.sh`.
