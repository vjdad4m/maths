# Graffiti.pc #189: only order fourteen remains at degree threshold five

Every finite connected simple graph for which at most one vertex has degree
below five and every vertex has at most six even-distance vertices (including
itself) has a spanning path unless its order is exactly fourteen. Equivalently,
any counterexample under those hypotheses has order fourteen. The conjecture
at that order and other degree thresholds are not settled by this theorem.

[DegreeFiveOnlyFourteen189.lean](DegreeFiveOnlyFourteen189.lean) combines the
[upper order bound](../graffiti-189-degree-five-order-fourteen/),
the [reduction to two-connected graphs](../graffiti-189-degree-five-reduction/),
and the formalization of [Easwar–Johari's small-order theorem](../graffiti-189-easwar-johari-order-two-d-plus-three/).
Its exact declaration is `Graffiti189LongestPath.order_eq_fourteen_of_degree_five_counterexample`.

For replay build those pinned packages under Lean and Mathlib 4.19.0,
prioritizing the compatibility ArticulationClique189 object in the reduction
package, and compile the source here with
`lean -j1 -DElab.async=false -DwarningAsError=true DegreeFiveOnlyFourteen189.lean`.
The [audit](VERIFIED.log) lists only the standard axioms.
