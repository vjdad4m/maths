# Kelmans F2: exact theta omission with an opposite edge retained

Consider the seven-vertex theta attachment in the exact cyclic-five
cubic setting of order four modulo six. Specify any genuine exterior
edge to omit. If at least one original opposite contact edge remains,
the required factor reduces to the smaller-order cyclic-four F2
promise. The cap is six vertices smaller, and the lift respects the
specified exterior edge even when it corresponds to a released wire.

The proof now covers zero, one, or two default replacement edges.
In the two-edge case, at least one of these edges is not the specified
omission. Symmetry and a choice between two caps preserve that edge,
while the other edge can be used to establish geometry without ever
being used in the transferred factor. The other original opposite
pair need not be a nonedge.

The precise theorem is
`ThetaDeadLeafCrossCover.released_exterior_if_one_retained_ear`.
The case with no original opposite contact edge retained, other
configurations, and the smaller-order F2 premise remain outside this
result; it does not settle Kelmans.

Use Lean 4.19.0 and Mathlib at
`c44e0c8ee63ca166450922a373c7409c5d26b00b` on `LEAN_PATH`.
Run `bash kelmans-theta-retained-ear/replay.sh` from the repository root.
