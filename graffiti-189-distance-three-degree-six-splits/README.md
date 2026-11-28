# Graffiti.pc #189: unbalanced splits at a degree-six cut endpoint

At the degree-five threshold, assume that each even-distance set (including
its center) has at most six vertices, deleting any single vertex preserves
connectivity, and at most one vertex has degree below five. Consider an
actual separating pair of vertices at distance three with a degree-six
member a and other member b.

The new routing theorem covers **every 2+4 split of a's neighbors** across
the two components. It imposes no order restriction or restriction on
b's neighbors. The actual-cut dispatcher also covers the balanced 3+3
split of a if b has four neighbors on one side. This includes rotating the
cut and the remaining singleton-port orientation, handled by a separate
rooted route. The only assumption the dispatcher leaves to its caller is
the balanced 3+3 split of a with at most three b-ports on each side.
This is not a proof of the full conjecture.

[Actual-cut dispatcher](DegreeFiveSixActualDispatch189.lean) ·
[2+4 routing theorem](DegreeFiveSixTwoFourFinal189.lean) ·
[Strict replay](StrictReplay.log).

Build the earlier degree-five, full distance-two, both-high endpoint, and
degree-seven/eight packages using Lean and Mathlib v4.19.0. Keep those object
roots on LEAN_PATH. Run the replay script from the complete source archive.
Exact direct predecessors are pinned by Git blob SHA in the archive.

[Complete pinned Lean sources](proof-sources.zip). Extract the archive and use its replay script.
