# Kelmans F2: exact theta omission even when erasing the opposite edge

Consider the seven-vertex theta attachment in the exact cyclic-five
cubic setting of order four modulo six. If at least one original
opposite contact pair is adjacent, then **every genuine exterior edge
omission** reduces to the smaller-order cyclic-four F2 promise.
The theorem includes the case in which the only such opposite edge
is the very edge to omit. The reduced instance has six fewer vertices.

For an erased opposite edge, its endpoints can still be absorbed into
the local picture to choose the smaller cap. An appropriate omission
within that cap rules out the tiling configurations that would require
the erased edge. The retained profiles lift without ever using it.

The precise main theorem is
`ThetaErasedEarOriginal.any_exterior_with_one_ear`. The theorem requires
neither an order-zero factor assumption nor that the other opposite
contact pair be a nonedge. The case where both opposite pairs are
nonedges is outside this theorem. This is a conditional F2 reduction,
not a proof of the Kelmans conjecture.

Use Lean 4.19.0 and Mathlib at
`c44e0c8ee63ca166450922a373c7409c5d26b00b` on `LEAN_PATH`.
From the repository root, run `bash kelmans-theta-erased-ear/replay.sh`.
