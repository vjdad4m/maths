# Graffiti.pc #189: at most 43 vertices at degree six and connectivity at least three

Let a finite simple connected graph have a vertex of degree at most six
and at most seven vertices at even distance from each vertex, including
itself. If it remains connected after deleting fewer than three vertices,
then it has **at most 43 vertices**. This cuts six vertices off the prior
uniform order bound; it is not a spanning-path theorem.

As in the preceding order bound, center at a vertex of degree at most six.
Let the positive even-depth vertices own their outward one-step children.
Their child sets together cover all odd vertices of depth at least three,
and each set has size at most six. If these sets cover more than 30 vertices,
then no two even-depth vertices can share an inward predecessor: the
shared predecessor would charge their combined children to one budget of
six positive even vertices, rather than two. In particular any three
second-layer vertices have separate chosen first-layer predecessors. Such
a triple exists by three-connectivity if the third layer is nonempty.
Each of the three chosen predecessors uses two slots outside its child
set, one for each other chosen predecessor or its child at depth two,
according to whether the predecessors are adjacent. Therefore three child
sets have size at most four, and at most three others have size at most six.
The combined coverage is at most 30, yielding the stated order bound.

Lean declaration:
`Graffiti189LongestPath.order_le_forty_three_at_degree_six_three_connected`.
Replay in Lean and Mathlib 4.19.0 with
[SixFiniteOrder189](../graffiti-189-degree-six-finite-order/) and its
prerequisites on LEAN_PATH. Check with `-DwarningAsError=true`.
The audit uses standard axioms only.
