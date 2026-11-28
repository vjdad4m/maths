# Graffiti.pc #189, degree six: the second shell has at least four vertices at order 25

Under the degree-six Graffiti hypotheses, if the graph is three-connected
and has order 25, every root of degree at most six has at least four
vertices at distance two. The main exact Lean theorem is
`Graffiti189LongestPath.four_le_second_shell_at_order25_degree_six`.
This is a structural restriction, not a spanning-path theorem.

With a second shell of size three, the radius-four reduction and exact
order count force six first, twelve third, and three fourth vertices.
The first-layer selectors partition the third layer into three four-vertex
groups with private representatives in the second layer. Every fourth-layer
site sees each group: degree at most six gives the selector's checked
radius-four bound, while degree above six makes the selector adjacent to
both other selectors and again supplies a route of length at most four.
The selector's exact even budget excludes distance four to the fourth
layer, so the route must have length three.

The root and all three fourth-layer sites spend four distance-two slots
at every representative. Missing spare first-layer neighbors force the
representatives to have an extra first-layer neighbor each, which forces
the three selectors into a clique. The other two selectors then use the
remaining slots at each representative, forbidding cross-group third-layer
edges. Every high third-layer vertex needs at least two fourth-layer
neighbors, since its degree within the union of its group and its private
representative is at most four. Any two pairs of fourth-layer sites
intersect. A high third-layer vertex therefore sees at least seven foreign
high vertices at distance two, more than its six available slots.

## Replay

Use Lean/Mathlib v4.19.0 and the
[order-25 radius package](../graffiti-189-degree-six-order25-radius/)
with all its predecessor objects in LEAN_PATH. Compile in the three-module
order shown in StrictReplay.log, using
`-j1 -s32768 -DElab.async=false -DwarningAsError=true`.
The axiom checks are standard only. No enumeration or solver is used.
