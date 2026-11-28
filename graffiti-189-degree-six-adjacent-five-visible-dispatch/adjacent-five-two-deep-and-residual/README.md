# Graffiti.pc #189: five visible, two balances with one deep vertex, and exact residual

For the degree-six order-16 adjacent singleton+13 cut, the original
finite graph is traceable with five visible vertices and two balanced
depth-two vertices, including the case of one deeper dark vertex.
There is no density hypothesis in the two-balance result.

When a common port sees both exclusive ports, the five strict dark
vertices and singleton exhaust its six positive-even slots. The
common port consequently sees all other visible ports, and every
low internal degree balance must be adjacent to it. This restores
the finite common-port certificates. The rooted strict/deep
six-vertex core avoids starting at the deep vertex by a checked
Ore-splice rotation. Dense internal cases use high-core closure;
sparse cases splice the two balances through the common ports.

The dispatcher combines this new theorem with the previously checked
two-balance no-deep, at-most-one-balance, and three-balance dark-dense
routes. The only possible five-visible exception is three balances
and a dark vertex of internal degree at most three.

Main declarations:
- Graffiti189LongestPath.CrossSaturation.ThresholdSix.traceable_of_adjacent_singleton_thirteen_five_two_balanced_with_deep
- Graffiti189LongestPath.CrossSaturation.ThresholdSix.traceable_of_adjacent_singleton_thirteen_five_unless_three_sparse

Dependencies: Lean/Mathlib 4.19, the earlier degree-five Ore/cut stack,
degree-six adjacent profile/ports and at-most-one-balance packages,
the two-balance no-deep package (including its small certificates),
and the three-balance dense package. Standard axioms only.
