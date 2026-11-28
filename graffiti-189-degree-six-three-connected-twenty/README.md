# Graffiti.pc #189: degree six, connectivity at least three, up to order 20

The theorem gives a Hamiltonian path in every connected finite simple graph on at most 20 vertices with vertex connectivity at least three, at most one vertex of degree below six, and at most seven vertices at even distance from every vertex (including itself).

At order 20 the [previous reduction](../graffiti-189-degree-six-three-connected-order20-frontier/) leaves nonspanning longest paths of length 13 or 14. This package excludes both via endpoint rotations and bounds on how many candidate endpoints can miss or hit vertices adjacent to the omitted set. Orders up to 19 use the [earlier theorem](../graffiti-189-degree-six-three-connected-nineteen/).

The entry point is `traceable_six_at_three_connectivity_order_twenty` in `SixThree20Final189.lean`. Lean 4.19.0, Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b. The final theorem uses only propext, Classical.choice and Quot.sound. This does not resolve the full conjecture.
