# Graffiti.pc #189: degree six and connectivity at least three imply order at most 24

Let G be finite, simple, and connected, with at most seven vertices
at even distance from each vertex, counting itself. Assume that deletion
of fewer than three vertices preserves connectivity, that all but at
most one vertex have degree at least six, and that there is a vertex
of degree at most six. Then G has at most **24 vertices**.

The universal joint parity cover bounds its order by 25. At order 25,
a degree-at-most-six root has eccentricity at most four and at least
four vertices in its second distance layer, by two preceding exact
theorems for three-connectivity. The exact radius-framed geometry
constructs a graph in one of the six Lean-refuted Fin 25 templates.
This bounds order, but does not settle the remaining spanning-path
cases at connectivity exactly three.

Main theorem:
`Graffiti189LongestPath.order_le_twenty_four_at_degree_six_three_connected`.
Use Lean and Mathlib 4.19.0. Replay with the checked objects from
[universal order 25](../graffiti-189-degree-six-order25-universal/),
[radius exclusion](../graffiti-189-degree-six-order25-radius/),
[second-shell exclusion](../graffiti-189-degree-six-order25-second-shell/),
and the certificates and geometry of the
[connectivity-four proof](../graffiti-189-degree-six-four-connected-complete/)
on LEAN_PATH. All audited axioms are standard only.
