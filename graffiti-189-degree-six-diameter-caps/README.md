# Graffiti.pc #189: degree-six diameter caps at connectivity two and three

Assume G is a finite connected simple graph with at most seven
vertices at even distance from each vertex, including itself.

- If fewer than two vertex deletions preserve connectivity, every
  pair is at distance at most **7**.
- If fewer than three vertex deletions preserve connectivity, every
  pair is at distance at most **5**.

The degree assumption is not needed once the even-distance cap is
fixed. If a geodesic reaches depth 8 (respectively 6), earlier even
layers 2,4,6 (respectively 2,4) are separators and supply at least
two (respectively three) vertices each. The root and the terminal
even vertex then raise the count to at least eight. This justifies
the distance cutoffs in a finite search, not its outcome.

Replay using Lean/Mathlib 4.19.0 and the checked
[SmallSeparator189](../graffiti-189-order-twelve/) object on LEAN_PATH:
`lean -j1 -DElab.async=false -DwarningAsError=true SixDiameterSeven189.lean`.
Both declarations use only standard axioms.
