# Graffiti.pc #133: a remote-neighbor restriction at an adjacent cycle gate

Let a finite simple graph have an induced seven-cycle and no induced
nine-vertex path. Suppose a vertex outside the cycle has exactly two
cycle contacts, and they are adjacent along the cycle. If a remote
vertex touches this gate, every remote neighbor of that vertex must
also touch the gate. Otherwise the two remote vertices, gate,
and a six-vertex cycle arc form an induced nine-vertex path.

With no four-cycle, this implies that such a remote vertex has at
most one remote neighbor. This is a structural restriction, not a
conclusion about the mean in the general nested case.

Use Lean 4.19.0 and Mathlib at
`c44e0c8ee63ca166450922a373c7409c5d26b00b` on `LEAN_PATH`.
Run `bash graffiti-133-nested-adjacent-gate/replay.sh` from the repository root.
