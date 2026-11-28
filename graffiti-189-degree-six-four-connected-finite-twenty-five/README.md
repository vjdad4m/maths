# Graffiti.pc #189: connectivity at least four and degree six imply order at most 25

A finite connected simple graph whose even-distance sets all have size
at most seven (including the center) has at most twelve vertices at
distance three from any vertex of degree at most six. If deleting fewer
than four vertices preserves connectedness, its diameter is at most
four and it has **at most 25 vertices**. The lemma does not itself give
a Hamiltonian path.

The third-layer vertices are covered by their distance-two sets from
first-layer vertices. Choose a smallest such cover, using t first-layer
vertices. Each selected first-layer vertex owns a private witness in
the third layer, and hence a second-layer vertex adjacent to no other
selected first-layer vertex. From any selected first-layer vertex,
each of the other t−1 selected vertices uses one distinct positive even
slot outside the third layer: either the other vertex itself if
nonadjacent (via the root), or its distinguished second-layer neighbor
if adjacent. Thus each cover member reaches at most 7−t third-layer
vertices. The complete third layer has size at most t(7−t) ≤ 12.
The root and even layers total at most seven, and the first layer at
most six, giving 7 + 6 + 12 = 25.

Lean declarations: `Graffiti189LongestPath.third_shell_le_twelve_at_degree_six`
and `Graffiti189LongestPath.order_le_twenty_five_at_degree_six_four_connected`.
Replay using Lean/Mathlib 4.19.0 with the previously checked
[SmallSeparator189](../graffiti-189-order-twelve/) on LEAN_PATH and
`lean -j1 -DElab.async=false -DwarningAsError=true SixFourFiniteOrder189.lean`.
Strict audit uses standard axioms only.
