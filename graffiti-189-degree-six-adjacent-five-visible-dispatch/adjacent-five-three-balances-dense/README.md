# Graffiti.pc #189: order 16, five visible, three balances, dense dark block

The degree-six threshold holds for an adjacent singleton+13 cut with
five visible ports, three balanced depth-two vertices, and dark
minimum degree at least four. Exact arbitrary original graph, not
only the labeled model. There is one deep vertex at distances (3,3);
both cut terminals use all six positive-even slots at distance two.

The common ports are connected without any dark-density assumption.
An isolated common would already see the other two commons and the
singleton at distance two. If it touched both exclusive ports, it
would also see the four strict vertices. If it touched just one,
degree six forces it to touch all three balances. It would then
see the deep vertex, the opposite exclusive and two strict vertices
at distance two as well. Either produces seven positive-even vertices.
Zero exclusive ports contradict degree six directly.

The dark block is Hamilton-connected under the additional density
hypothesis: use terminal Ore to fill every edge incident to its
five heavy core vertices, which boosts every vertex to degree at
least five. A spanning path of the common triple can then be
spliced through an attached balance, or through the unused exclusive
if its first common has no balance neighbor.

Main declaration:
Graffiti189LongestPath.CrossSaturation.ThresholdSix.traceable_of_adjacent_singleton_thirteen_five_three_balanced_dark_dense.

Replay Lean/Mathlib 4.19 with the earlier q=2 no-deep, positive profile
and Ore packages on LEAN_PATH. Only standard axioms.
