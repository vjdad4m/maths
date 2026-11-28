# Graffiti.pc #189: spanning paths through two adjacent-cut shores

Let G be a finite simple graph that stays connected after deletion of any one vertex and has at most one vertex of degree less than five. Suppose adjacent vertices a,b separate G into two connected shores. This package gives spanning paths for bounded shore sizes; it assumes neither a parity cap nor that a,b are twins.

If one shore has 2–7 vertices and the other has 2–8, G has a spanning path. In particular, this holds at orders 14–16 whenever both shores have at least six vertices, and at order 17 when both shores have at least seven vertices. See `traceable_of_mixed_adjacent_two_shores_seven_eight` and `traceable_of_mixed_adjacent_balanced_order_le_seventeen`.

The route uses rooted Ore closure within an augmented shore. Adding one cut vertex leaves each high shore vertex with degree at least four, enough for order at most eight. With both cut vertices added, high shore vertices retain degree five, enough for order at most ten. After closing the high clique, the only low shore vertex, if present, can be inserted at the start or as the other endpoint of a spanning path. The other shore is entirely high and supports either terminal orientation. Finally, the two disjoint paths are joined along a terminal edge.

The declarations are in namespace `Graffiti189LongestPath.CrossSaturation.FiveAdjacent`. This is a partial result, not a proof of Graffiti.pc #189 in general.

Use Lean 4.19.0 with Mathlib 4.19.0 and the already checked dependency objects on `LEAN_PATH`. Direct external source modules in `vjdad4m/maths` are:

* `graffiti-189-adjacent-exact-two-shores/AdjacentCutFiveComponents189.lean` (also in the adjacent-cut-structure release),
* `graffiti-189-degree-five-cuts/src/DegreeFiveSmallSides189.lean`,
* `graffiti-189-adjacent-twins-fourteen/RootedOreTwoRootsNonedge189.lean`.

Run `./replay.sh`. See `LEAN-CHECK.txt` for the standard axiom audit.
