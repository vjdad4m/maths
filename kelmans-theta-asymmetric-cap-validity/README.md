# Kelmans F2: exact validity in the asymmetric faithful layout

For a cubic, cyclically five-edge-connected ambient graph with the
exact enlarged theta layout, assume the four surviving original
contacts are distinct. The other exterior contacts may coincide
with earlier sites subject to the listed graph conditions. The
revised cap from the [asymmetric route](../kelmans-theta-asymmetric-faithful/)
is cyclically four-edge-connected exactly when the original port
pairs p2–p3 and p1–p4 are both nonedges.

With the appropriate order residue, that gives the exact factor
after the original root and specified exterior edge omission from
smaller cyclic-four F2 on six fewer vertices. In the no-opposite-edge
case, p1–p4 is already a nonedge, leaving the single adjacent-port
test p2–p3. No conclusion here for that remaining adjacent-port
case or for the full Kelmans conjecture.

Main theorems: `ThetaAsymmetricFaithfulScope.cap_valid_iff_two_edges_absent`
and `ThetaAsymmetricFaithfulScope.reduce_of_four_contacts`.

Use Lean 4.19.0 and Mathlib at
`c44e0c8ee63ca166450922a373c7409c5d26b00b` on `LEAN_PATH`.
From repository root run `bash kelmans-theta-asymmetric-cap-validity/replay.sh`.
