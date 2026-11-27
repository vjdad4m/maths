# Graffiti.pc #189: the four-omission order-15 case

In the 2-connected degree-four case, Lean proves traceability whenever
an edge-optimal longest path has ten edges, omits four vertices, and has
endpoints of degree at least four. Edge-optimal means maximizing the
number of edges induced by the omitted vertices among longest paths.

If an omitted vertex has two attachments to the path, the endpoint
distance-two budgets rule out the resulting structure. Otherwise a
small verified model records the two attachment positions and exact
endpoint neighborhoods. Lean checks all 21 possible pairs of positions
in independent row groups. These are finite certificates for a reduced
model, not enumeration of all 15-vertex graphs.

The main theorem is `traceable_if_four_off_order_fifteen`. This does
not resolve the remaining one-omission order-15 branch or all of #189.
Use Lean 4.19.0 and Mathlib at `c44e0c8ee63ca166450922a373c7409c5d26b00b`
on `LEAN_PATH`, then run
`bash graffiti-189-order-fifteen-four-off/replay.sh` from the repo root.
