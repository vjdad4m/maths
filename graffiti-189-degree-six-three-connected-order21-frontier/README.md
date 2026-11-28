# Graffiti.pc #189: longest-path reduction at order 21

Let a connected simple graph have 21 vertices, vertex connectivity at least three, at most one vertex of degree below six, and at most seven vertices at even distance from each vertex (including itself). Lean proves that any nonspanning longest path has 13, 14, or 15 edges. This is a reduction, not a full traceability proof.

The entry point is `longest_shape_at_twenty_one` in `SixThree21Frontier189.lean`. The prerequisites are in the [order-20 result](../graffiti-189-degree-six-three-connected-twenty/) and its dependencies. Lean 4.19.0 and Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b; standard axioms only.
