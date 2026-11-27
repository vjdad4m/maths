# Graffiti.pc #189: the two remaining order-16 branches

For the 2-connected degree-four case, Lean proves that a nontraceable
graph on at most 16 vertices must have order exactly 16 and admit an
edge-optimal longest path that omits either four or five vertices.
The path lengths are eleven and ten, respectively. The theorem
`order_sixteen_two_remaining_branches` reuses the full order-15 result
and closes the other possibilities.

The three-omission branch uses a structural boundary analysis and 12
small kernel-checked rows for interior attachment positions. Endpoint
distance-two bounds exclude the exceptional labeled pattern before
the final graph transfer. A separate length-nine argument and the
previous saturated case eliminate the six- and seven-omission branches.

Neither of the remaining four- and five-omission branches is claimed
here. Thus order 16 and general #189 remain unresolved.

Use Lean 4.19.0 and Mathlib at `c44e0c8ee63ca166450922a373c7409c5d26b00b`
on `LEAN_PATH`, then run `bash graffiti-189-order-sixteen-shape/replay.sh`
from the repository root.
