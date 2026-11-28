# Graffiti.pc #189: any degree-five counterexample has order at most fifteen

At the degree-five threshold, a connected finite simple graph has at most one vertex of degree below five, and at most six even-distance vertices from each vertex, counting itself. Every such graph of order at least sixteen has a spanning path. Equivalently, any counterexample at this threshold has order at most fifteen. This does not address the degree-four or other threshold branches in general.

The public declarations are `Graffiti189LongestPath.order_le_fifteen_of_degree_five_counterexample` and `Graffiti189LongestPath.traceable_at_degree_five_of_order_ge_sixteen`.

Use the already checked reduction to a genuine adjacent cut, the exact two-component theorem, and the previous ≤16 bound. At order sixteen the nonsingleton adjacent-cut dispatcher applies unless a shore is a singleton; then the checked singleton geometry provides a nonadjacent separator, and the checked nonadjacent dispatcher yields the required path. The intermediate declaration is `Graffiti189LongestPath.CrossSaturation.FiveAdjacent.traceable_of_actual_adjacent_two_shores_order_sixteen`.

Use Lean 4.19.0 with Mathlib v4.19.0 and the previously checked dependency objects available on `LEAN_PATH`. Run `./replay.sh`; `LEAN-CHECK.txt` lists the audited declarations.

The source bundle contains ten new modules: the order-16 profile and singleton proofs, the order-15 (4+9) nonsingleton route, the combined nonsingleton route, and the final global cap. See [the final theorem](AdjacentCutFiveMixedCapFifteen189.lean) and [strict replay records](VERIFIED.log). Predecessor objects come from the [order-16 cap](../graffiti-189-degree-five-order-sixteen/), [exact two-shore reduction](../graffiti-189-adjacent-exact-two-shores/), [mixed routing](../graffiti-189-adjacent-mixed-routing/), [unequal large-shore routes](../graffiti-189-adjacent-unequal-large-routing/), and [nonadjacent cuts](../graffiti-189-full-nonadjacent-cuts/). As in the degree-five reduction, put its compatibility copy of ArticulationClique189 before older objects. The combined transcript records successful strict serial stages.

[Complete pinned Lean sources](proof-sources.zip). Extract the archive and use its replay script.
