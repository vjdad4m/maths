# Graffiti.pc #189: excluding the 6+13 distance-three split at degree six

Lean rules out a six-vertex shore opposite a thirteen-vertex shore at
an actual two-cut whose terminals are at distance at least three.
Combined with the earlier order-20 result, the order-at-most-21
dispatcher leaves only the 7+12 and 8+11 shore splits unresolved.

The six-shore is forced to be a clique. Terminal-visibility roles,
local adjacency constraints, and the two cut terminals' degree and
even-distance budgets reduce the thirteen-shore to 60 labeled profiles.
Each formula uses only required local D2 charges, exact port visibility,
and a clause enforcing that any nonempty hidden block has an edge to
the rest of the connected shore. Three relaxed profiles need this last
constraint. Every LRAT derivation and the graph-to-formula transfer
are checked by Lean with only standard axioms.

Main declarations in Graffiti189LongestPath.CrossSaturation.ThresholdSix:
- no_six_thirteen_shores
- traceable_or_seven_twelve_eight_eleven_at_six_distance_three_order_twenty_one
