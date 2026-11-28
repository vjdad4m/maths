# Graffiti.pc #189: normalized singleton order-16 route, at most two balances

For the explicitly defined normalized Fin 16 board with two unique exclusive
ports, four common ports, and seven dark vertices, this package proves a
spanning path when at most two dark vertices are balanced. The two strict
classes have at least two vertices each; every strict vertex has at least
five neighbors within the dark block. All allowed internal edges remain
arbitrary, subject to the exact Frame boundary and degree assumptions and
the given even-distance cap. The graph-to-board classification is a separate
step and not assumed proved by this package.

Even-distance saturation forces minimum degree two in the common block. If
all balanced vertices have dark degree at least three, terminal Ore closes the
edges from them into the strict block and proves Hamilton connectivity of the
dark block. Otherwise remove a low balanced vertex. The remaining dark block
is Hamilton-connected; the removed vertex attaches to the common ports,
either as a bridge from the dark block or after the opposite exclusive port
if it has no dark neighbor. The finite constants only check disjoint support
and that the final path covers all sixteen labels.

Main checked theorem:
Graffiti189LongestPath.CrossSaturation.ThresholdSix.Singleton16.traceable_of_normalized_singleton_at_most_two_balanced.
Use Lean and Mathlib 4.19.0 with earlier checked cut and Ore objects, including
the nonsingleton order-16 package and ResidualOreParam189, on LEAN_PATH.
