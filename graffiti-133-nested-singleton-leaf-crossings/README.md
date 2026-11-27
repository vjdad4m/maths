# Graffiti.pc #133: unrestricted numbers of singleton-leaf crossings

In a finite graph with no four-cycle and no induced nine-vertex
path, consider an induced seven-cycle and a protected set.
Every vertex outside the protected set is either remote from
the cycle or a degree-at-most-two leaf with exactly one cycle
contact. Every remote outside the protected set must touch such a
leaf, the leaf must not be shared by two remote vertices, and the
remote's neighbors in the protected set lie at most at two
designated vertices.

With these exact attachment hypotheses, Lean proves that the
whole graph's signed excess over mean four is at most the protected
set's. No numerical cap on the number of such leaf crossings is
needed. A corollary handles a protected base dominated by the
seven-cycle with at most four multiple-contact vertices.

A remote neighbor of a vertex touching a singleton-cycle gate
must itself see the gate, or there is an induced nine-vertex path.
The unshared leaves make the remote layer independent, so it
can be peeled after the leaves. The exact main theorem is
`Graffiti133NestedSingleGate.arbitrary_singleton_leaf_crossings_preserve_score`.
This does not settle arbitrary attachments or general #133.

Use Lean 4.19.0 and Mathlib at
`c44e0c8ee63ca166450922a373c7409c5d26b00b` on `LEAN_PATH`.
Run `bash graffiti-133-nested-singleton-leaf-crossings/replay.sh` from the repository root.
