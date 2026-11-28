# Graffiti.pc #189, d=6: eccentricity at most four at orders 24 and 25

Let G be a finite connected simple graph with at most seven even-distance
vertices from each vertex, at most one vertex of degree below six, and
connectivity preserved upon deleting fewer than three vertices. If G
has at least 24 vertices, then every degree-at-most-six vertex has
eccentricity at most four. The exact theorem is
`Graffiti189LongestPath.eccentricity_le_four_of_order_ge_twenty_four_at_degree_six`.
This excludes a geometric branch; it is not a spanning-path theorem.

A depth-five vertex forces exactly three vertices at each even depth
two and four. The joint odd-layer charge gives three selectors with
near representatives and at least eleven covered far vertices.
Their three far budgets each have size at most four.

If all three far budgets are full, a fourth-layer site with a
forward neighbor can receive routes from at most two selector groups:
the fifth-layer neighbor would otherwise spend a slot in all three.
One active group or two active groups force both a selector and its
representative below degree six, a contradiction.

If one group is deficient, it has size three and all three groups are
disjoint. Every fourth-layer site with a forward neighbor is active
for exactly one group, and that group cannot be the deficient one.
The saturated inactive group's charge forces the active representative
below degree six, making the active selector high. It must be adjacent
to the deficient selector. The fourth-layer site then has distance
exactly four from the deficient selector and spends its one spare even
slot. There can be at most one fourth-layer site with a forward
neighbor, yet deleting these sites separates the root from depth five,
contrary to three-connectivity.

## Replay

Use Lean/Mathlib v4.19.0. Place the
[order-25 radius package](../graffiti-189-degree-six-order25-radius/)
and all its imported modules in LEAN_PATH. Replay the six modules in
StrictReplay.log order using `-j1 -s32768 -DElab.async=false -DwarningAsError=true`.
Only the three standard Lean axioms; no enumeration or solver is used.
