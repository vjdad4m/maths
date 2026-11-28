# Graffiti.pc #189: the remaining order-fifteen singleton profile

Suppose a finite connected simple graph remains connected after deleting any one vertex, no vertex has more than six vertices at even distance (including itself), and at most one vertex has degree below five. An adjacent two-vertex cut leaves two shores of sizes one and twelve. Lean shows that it either has another, nonadjacent two-vertex separator, or the twelve-vertex shore has the single six-class profile (3,3,1,1,1,3).

The six classes are the even-depth vertices nearer the first terminal, nearer the second terminal, and equally near both, followed by the three corresponding odd-depth classes. The known nonadjacent-cut theorem applies in the first outcome. The balanced profile in the second outcome remains open in this package.

The main graph theorem is `Graffiti189LongestPath.CrossSaturation.FiveAdjacent.alternate_cut_or_balanced_of_adjacent_singleton_twelve_shores`, in [AdjacentCutFiveFifteenSingletonResidual189.lean](AdjacentCutFiveFifteenSingletonResidual189.lean). Use Lean and Mathlib 4.19.0 with the earlier checked adjacent-cut and order-16 profile objects on LEAN_PATH. Compile in order.txt order with `-j1 -DElab.async=false -DwarningAsError=true`. The [audit](LEAN-CHECK.txt) permits only standard axioms.

External imports also use the [order-14 singleton frontier](../graffiti-189-order-fourteen-singleton-frontier/) and the [order-15 cap source bundle](../graffiti-189-degree-five-order-fifteen/) for the previously checked mixed-shore geometry.
