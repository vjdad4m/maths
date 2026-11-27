# Graffiti.pc #189: the five-omission order-15 case

This Lean proof rules out an edge-optimal longest path with nine edges and
five omitted vertices in the degree-four, 2-connected case of #189 when
both endpoints have degree at least four. Edge-optimal means maximizing the
number of edges among the omitted vertices, subject to the path being longest.
The proof handles both one and two path attachments per omitted vertex and
does not enumerate labeled graphs. The exact conclusion is
`no_five_off_length_nine`; other order-15 cases remain open.

Use Lean 4.19.0 with Mathlib at `c44e0c8ee63ca166450922a373c7409c5d26b00b`
and an existing Mathlib `LEAN_PATH`, then run
`bash graffiti-189-order-fifteen-five-off/replay.sh` from the repository root.
