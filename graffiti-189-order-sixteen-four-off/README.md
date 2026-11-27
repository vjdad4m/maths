# Graffiti.pc #189: excluding four omissions at order 16

Under the degree-four and 2-connectivity hypotheses, suppose every
vertex has at most five vertices at even distance, counting itself.
Given the edge-optimal high-endpoint path from the earlier reduction,
this package proves that a longest path of length 11 edges omitting
exactly four vertices implies a Hamiltonian path.

The proof splits into the cases where an omitted vertex has two path
contacts and where all omitted vertices have at most one. Both have
exact graph-to-finite-model transfer proofs. The second uses 49
independently kernel-checked certificate partitions assembled into
16 rows and a final dispatcher. The small anomalous profiles are
excluded using their distance-two budgets in the actual graph.

The main theorem is
`Graffiti189LongestPath.TwoCut.SmallOrderFour.traceable_if_four_off_order_sixteen`.
Together with the [two remaining branches reduction](../graffiti-189-order-sixteen-shape/),
this rules out the four-omission branch; the five-omission branch and
the general conjecture remain open. This is not a proof for all
graphs on 16 vertices.

Use Lean 4.19.0 and Mathlib at
`c44e0c8ee63ca166450922a373c7409c5d26b00b` on `LEAN_PATH`.
Run `bash graffiti-189-order-sixteen-four-off/replay.sh` from the
repository root. The replay generates exact Lean files and
checks their hashes before proving them in separate processes.
