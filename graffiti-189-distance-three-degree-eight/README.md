# Graffiti.pc #189: distance-three cuts with a degree-eight endpoint

**Lean-checked partial result.** Let a finite connected simple graph
stay connected after any single vertex is deleted. Suppose each
even-distance set, including its center, has at most six vertices,
and at most one vertex has degree below five. If a separating pair
is at distance three and one member has degree eight, the graph
has a Hamiltonian path. The other endpoint's degree is not assumed,
and there is no order restriction.

The four-port cap forces four neighbors of the degree-eight endpoint
onto each shore. A port on a shortest route across the two cuts
determines a terminal route on its shore. The other shore is routed
using either another such bridge or the unique gateway supplied by
the local distance-two budget. The proof joins the shores in the
original graph. The endpoint may be swapped before using the theorem.

[Main Lean theorem](src/DegreeFiveEightActual189.lean) · [Strict replay](StrictReplay.log)

To replay, build the [degree-five baseline](../graffiti-189-degree-five-cuts/)
and [additional cut modules](../graffiti-189-degree-five-more-cuts/) in
Lean and Mathlib v4.19.0. Put their object roots on LEAN_PATH and run
`lake env bash /path/to/replay.sh`.
The exact direct predecessor Git blobs are in [PINNED-BASELINES.tsv](PINNED-BASELINES.tsv).

The other not-yet-checked distance-three branches and unrestricted #189
are not resolved by this package.
