# Graffiti.pc #189, degree six: order at most 25 without a connectivity threshold

Let G be a finite connected simple graph in which each vertex has at most
seven vertices at even distance from it, counting the vertex itself.
If G contains any vertex of degree at most six, then G has order at most
25. No lower bound on degrees or on vertex connectivity is needed.
This is an order reduction, not a spanning-path result.

The exact Lean theorems are
`Graffiti189LongestPath.far_odd_card_le_twelve_at_degree_six` and
`Graffiti189LongestPath.order_le_twenty_five_at_degree_six`.

At a root x of degree at most six, choose a minimum-cardinality family T
from its neighbors whose distance-two sets cover its third layer. For
each a in T, other selected neighbors or their private second-layer
representatives account for |T|−1 distinct even-distance vertices at
a. Those are at depth at most two from x. Every odd-depth vertex y
with depth m≥3 is at distance exactly m−1 from a selected neighbor:
choose one whose distance-two shell contains the third vertex on a
shortest x-to-y path, use its geodesic suffix, and apply the triangle
inequality. Hence all far odd vertices share a total budget at most
|T|(7−|T|)≤12. Root-even vertices and root neighbors add at most 7+6.

## Replay

Use Lean/Mathlib v4.19.0 with the object closure of `SmallSeparator189`
on LEAN_PATH. Compile `src/SixUniversalOrder25Middle189.lean` with
`-j1 -s32768 -DElab.async=false -DwarningAsError=true`.
The included axiom report records only standard Lean axioms.
