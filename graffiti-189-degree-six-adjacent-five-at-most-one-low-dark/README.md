# Graffiti.pc #189: five-visible order-16 residual requires two low balances

The original-graph degree-six adjacent singleton+13 and five-visible
case is now traceable unless three dark vertices are balanced and at
least two of these have induced dark degree at most three. This is
the narrowest checked five-visible reduction in this series.

Any single low balance can attach to an endpoint of a path through
the common triple. If both endpoints of a common chain missed it,
the low balance would have to touch both exclusive ports and the
middle common; this lets a chain endpoint see too many vertices at
distance two. For a degree-three low balance, a weighted high-core
Ore path ends there. For a degree-one or degree-two low balance,
delete it temporarily: if two remaining degrees drop to three,
the five-vertex high core is unaffected by the deletion and
seven-vertex high-core Ore closure applies. Otherwise use at most
one weighted terminal.

Main declarations:
- Graffiti189LongestPath.CrossSaturation.ThresholdSix.traceable_of_adjacent_singleton_thirteen_five_three_balanced_exactly_one_low
- Graffiti189LongestPath.CrossSaturation.ThresholdSix.traceable_of_adjacent_singleton_thirteen_five_unless_two_low

Replay Lean/Mathlib 4.19 with the earlier singleton, Ore, q=2
and q=3 dense packages on LEAN_PATH. Standard axioms only.
