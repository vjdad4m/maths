# Graffiti.pc #189: degree six and connectivity at least three through order 19

A finite simple connected graph on at most 19 vertices has a spanning
path if deleting fewer than three vertices preserves connectedness,
there is at most one vertex of degree below six, and each vertex
has at most seven even-distance vertices, including itself.

At the new order, a longest nonspanning path with two high endpoints
and length at most thirteen has at most one free slot among the
endpoint marks. Two pins on an omitted vertex force both endpoints to
see a pin, and at least one to see all its pins. Rotating the endpoints
and counting their distance-two vertices rules out this one-hole case.
For a longer path the four-vertex high-omitted shape again fills its
even budget, prohibiting too many endpoint marks. It then suffices to
exclude a unique low omitted vertex. At the exceptional length
seventeen, at least one extreme pin must survive each rotation; either
one or both extreme pins then contradict the endpoint degree.

Main: `Graffiti189LongestPath.SixThreeNineteen.traceable_six_at_three_connectivity_order_nineteen`.
Use Lean/Mathlib 4.19.0 and
[order-18 predecessor objects](../graffiti-189-degree-six-three-connected-eighteen/)
on LEAN_PATH. Compile the eleven modules in order in StrictReplay.log.
Only standard axioms are used. This does not settle higher orders.
