# Graffiti.pc #189, d=6: every degree-at-most-six root has eccentricity ≤4 at order 25

For a 25-vertex connected graph under the even-distance cap of seven,
assuming deletion of any set of fewer than three vertices remains connected
and at most one vertex has degree below six, each vertex of degree at most
six has no vertex at distance five or more. This rules out the entire
radius-five order-25 branch of the degree-six three-connected problem.
It does not prove a spanning path in the remaining order-25 radius cases.

The top-level theorem is
`Graffiti189LongestPath.eccentricity_le_four_at_order25_degree_six`.

If there is a depth-five vertex, both the second and fourth layers have
size three. The tight combined odd-layer charging proof has three selected
neighbors, with bijective distinct representatives at depth two. The far
odd sets are disjoint groups of four. Exact even-budget saturation rules
out an additional even distance outside the four far charges and two
private near charges. Fix a depth-four predecessor of a depth-five vertex;
its third-layer neighbors must all lie in the same group. The two other
selected vertices cannot have distance three or four to this predecessor.
This forces both the selected vertex in the corresponding group and its
depth-two representative to have degree below six. The threshold forbids
two such vertices.

## Replay

Use Lean/Mathlib v4.19.0, compile the four modules in StrictReplay.log order.
Put the object closure of [the order-25 three-connected package](../graffiti-189-degree-six-order25-three-connected/)
and `SixTripleCutBasics189` from
[the initial three-cut package](../graffiti-189-degree-six-three-cut-count/)
on LEAN_PATH. Compile with
`-j1 -s32768 -DElab.async=false -DwarningAsError=true`.
All printed axiom lists contain only the three standard Lean axioms.
