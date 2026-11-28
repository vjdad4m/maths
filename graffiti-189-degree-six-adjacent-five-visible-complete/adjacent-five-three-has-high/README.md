# Graffiti.pc #189: five visible, any high balance

In the degree-six adjacent singleton+13 case, five visible vertices
with three balanced dark vertices yield a spanning path if any
balance has dark degree at least four. No restrictions on the two
other balances. Thus the only potential five-visible obstruction
has three balances all of dark degree at most three, with at least
one of degree at most two.

A tiny balance can be appended to a seven-vertex dark path when a
second balance has degree three; a marked low endpoint is handled
by two-stage Ore closure. For two tiny balances, if adjacent,
deleting both costs at most two degrees in total from any pair
of other vertices, so the six-vertex dark remainder is
Hamilton-connected. If nonadjacent, the remainder satisfies rooted
Ore; a two-end avoidance rotation starts at a strict vertex. Each
tiny balance meets at least two common ports, and a kernel-checked
small common/port certificate interleaves the second one.

Main:
Graffiti189LongestPath.CrossSaturation.ThresholdSix.traceable_of_adjacent_singleton_thirteen_five_three_balanced_has_high.

Replay Lean/Mathlib 4.19 with all previous adjacent singleton
packages, including the small-balance residual, on LEAN_PATH.
Standard axioms only.
