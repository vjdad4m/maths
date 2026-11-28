# Graffiti.pc #189: degree six and connectivity at least three through order 18

Under the degree-six threshold, cap of seven even-distance vertices
counting the center itself, and connectivity after deleting fewer
than three vertices, every graph on at most eighteen vertices has a
spanning path. It is not the unrestricted degree-six theorem.

A longest nonspanning path can be rotated to two high endpoints.
If it has exactly twelve edges, the endpoint marks partition all
slots. Same-support rotations put too many vertices at distance two
from a fixed outside vertex, forcing the unique low vertex onto the
path. Further charges from the active outside vertices then exceed a
high endpoint's even-distance budget. This length-twelve obstruction
is independently proved whenever there are three distinct active
outside vertices, without any order bound.

For a longer path at this order, a high omitted vertex would force
the four-vertex tight outside set and three pins. Rotation prohibits
two endpoint-mark slots, a contradiction. The only remaining omitted
vertex is the unique low one. Endpoint mark equality forces both
extreme pins after every rotation, incompatible with a high endpoint
having six neighbors.

Main declaration:
`Graffiti189LongestPath.SixThreeEighteen.traceable_six_at_three_connectivity_order_eighteen`.
Use Lean/Mathlib 4.19.0 and
[order-17 predecessor objects](../graffiti-189-degree-six-three-connected-seventeen/)
on LEAN_PATH. Compile the nine modules in order from StrictReplay.log.
Only standard Lean axioms are used.
