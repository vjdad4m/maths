# Graffiti.pc #189: radius-five constraint at degree six and connectivity three

Let G be a finite simple connected graph with at most seven vertices
at even distance from any vertex (including itself). Suppose deleting
fewer than three vertices preserves connectivity, and x has degree at
most six. Then the order is at most **40**. If the order exceeds 25,
x has eccentricity exactly five and its second and fourth distance
layers each contain exactly three vertices. Both layers separate x
from the vertices at distance five.

Connectivity and the even cap rule out distance six: the second and
fourth layers each cost at least three positive even slots, and a
distance-six vertex would cost a seventh. The third layer has at most
12 vertices by the preceding minimum-cover theorem. Each vertex of
the fourth layer accounts for at most five fifth-layer children:
an inward third-layer predecessor sees them all at distance two
and must also spend one slot on a geodesic vertex at distance one
from x. Adding root, neighbors, and the remaining layers gives
7 + 6 + 12 + 15 = 40. This is a structural reduction, not a spanning
path theorem.

Lean declarations:
`Graffiti189LongestPath.outer_shell_profile_at_degree_six_three_connected`
and `Graffiti189LongestPath.order_le_forty_at_degree_six_three_connected`.
Use Lean/Mathlib 4.19.0 and
[SixFourFiniteOrder189](../graffiti-189-degree-six-four-connected-finite-twenty-five/)
with its prerequisites on LEAN_PATH. The strict log audits only
the standard axioms.
