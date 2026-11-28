# Graffiti.pc #189, degree six: order ≤25 for three-connected graphs

For every finite connected simple graph with at most seven vertices at
even distance from each vertex, and any root x of degree at most six,
the third and fifth distance layers around x have combined size at
most twelve. There is no diameter assumption in this first result.

If additionally deleting fewer than three vertices leaves the graph
connected, the graph has order at most 25. These are
`Graffiti189LongestPath.third_and_fifth_shells_le_twelve_at_degree_six`
and `Graffiti189LongestPath.order_le_twenty_five_at_degree_six_three_connected`.
This does not itself prove a spanning path for the remaining graphs.

Choose an inclusion-minimal cardinality set T of roots in the first layer
whose distance-two sets cover the third layer. For each a in T the minimality
gives a private middle representative in layer two. The other T vertices
or their private representatives give |T|−1 distinct distance-two charges
at a in layers one and two. Every vertex at depth five is at distance four
from some a in T, by appending two edges to a distance-two route from a
to the third vertex on a shortest path at depth five. These charged fifth
layer vertices and the covered third layer vertices both spend the even
budget. There are at most |T|(7−|T|)≤12 combined vertices. The checked
radius-five reduction then gives order at most 7+6+12=25.

## Replay

Use Lean/Mathlib v4.19.0. Place the `SixThreeRadiusFive189` object
and its finite-order proof predecessor closure on LEAN_PATH.
Compile `src/SixThreeJointOrder189.lean` with
`-j1 -s32768 -DElab.async=false -DwarningAsError=true`.
Both axiom checks in StrictReplay.log report only standard Lean axioms.
