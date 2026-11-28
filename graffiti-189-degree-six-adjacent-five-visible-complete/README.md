# Graffiti.pc #189: complete five-visible branch of the order-16 adjacent singleton split

At the degree-six threshold, suppose an adjacent two-vertex separator
leaves a singleton and a 13-vertex component. If exactly five vertices
of the larger component are adjacent to the separator, Lean proves a
Hamiltonian path, with no further degree or balance hypothesis.

The final branch uses counting and a fixed-terminal Ore route for the
five-vertex dark core, then a proof-term LRAT certificate for 49 tails.
The original graph transfer is checked. Nothing needs a native decision
axiom or a SAT solver at replay time.

Replay the `adjacent-five-three-has-high` dependency and then
`adjacent-five-visible-complete`, in the module order in each directory,
with Lean/Mathlib 4.19.0 and earlier checked prerequisites on LEAN_PATH.
See the supplied axiom logs and source checksums. The six-visible
positive-balance, multiple-exclusive cases are separate.
