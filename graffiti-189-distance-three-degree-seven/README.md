# Graffiti.pc #189: distance-three cuts with a degree-seven endpoint

**Lean-checked partial result.** Let a finite connected simple graph stay connected
after any single vertex is deleted. Suppose each even-distance set, counting
its center, has at most six vertices, and at most one vertex has degree below
five. If a separating pair is at distance three and one member has degree
seven, the graph has a Hamiltonian path. The other endpoint's degree is not
assumed and there is no order restriction.

The cap of four ports on each shore forces a three/four split for the
degree-seven endpoint. The argument reuses the degree-eight route to
traverse the four-port shore, with its starting bridge chosen to leave a
viable shore route at the three-port side. On the latter side the numbered
local, alternating, and bridge routes handle the small interior and the
case where the routes at the two cut vertices have different port counts.

[Main Lean theorem](src/DegreeFiveSevenActual189.lean) · [Strict replay](StrictReplay.log)

Replay with Lean and Mathlib v4.19.0. First build the shared predecessors linked
from the [distance-two](../graffiti-189-full-distance-two/) and
[degree-eight](../graffiti-189-distance-three-degree-eight/) bundles and those
bundles themselves. Put those object roots on LEAN_PATH and run
`lake env bash /path/to/replay.sh`. See [exact direct inputs](PINNED-BASELINES.tsv).

This does not settle the unrestricted conjecture.
