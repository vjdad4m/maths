# Graffiti.pc #189: five visible, two balanced and no deep vertices

For the degree-six threshold at order 16, an adjacent actual two-cut
with a singleton and a thirteen-vertex shore is traceable if the large
shore has five visible ports, two balanced dark vertices and no deep
vertex. This is an original-graph theorem with explicit Fin16 labeling
and transport. There is no dark induced minimum-degree premise.

The strict core contains six vertices, three of either color. When both
balances have dark degree at least four, use a weighted terminal Ore
route to a balance. With one lower balance, route the other seven first
and attach the low balance. With two lower balances, a rooted Ore path
of the strict core permits a sparse balance/common splice. The small
port skeleton certificates are checked by Lean kernel reduction, with
no native computation axiom. Separate normalized cases cover an edge
between the two balances, no such edge, and absence of their strict
neighbors.

Main theorem:
Graffiti189LongestPath.CrossSaturation.ThresholdSix.traceable_of_adjacent_singleton_thirteen_five_two_balanced_no_deep.

Replay with Lean/Mathlib 4.19 and the earlier Ore, singleton geometry,
parity profile and port-score packages on LEAN_PATH. Standard axioms
only. The five-visible cases with a deep vertex and the six-visible
positive multi-exclusive cases are not resolved by this package.
