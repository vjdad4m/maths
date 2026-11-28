# Graffiti.pc #189: exclude length 13 at order 21

For the degree-six, connectivity-at-least-three branch on 21 vertices, Lean now proves that any nonspanning longest path has 14 or 15 edges. Neither of those lengths is excluded here.

At length 13, rotation and the even-distance cap allow at most one path neighbor per omitted vertex. The high-degree omitted vertices then admit a long path between any prescribed pair by the two-terminal Ore theorem. The path can also be extended to use a low-degree omitted terminal when needed. Splicing forces the attachment vertices on the original longest path to be too far apart.

The entry point is `longest_shape_at_twenty_one_reduced` in `SixThree21ThirteenClose189.lean`. Prerequisites: [order-21 frontier](../graffiti-189-degree-six-three-connected-order21-frontier/) and the [degree-five cuts package](../graffiti-189-degree-five-cuts/) for `TwoTerminalOre189`. Replayed with Lean 4.19.0 and Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b; standard axioms only.
