# Kelmans F2: the only residual small cut in the asymmetric cap

In the exact cubic cyclic-five asymmetric faithful layout, assume the
four surviving original contacts are distinct and p1–p4 is absent.
Do not assume that p2–p3 is absent. Lean checks that every
nontrivial cut of width at most three in the revised cap has one
shore exactly the proposed cap vertex A together with p2 and p3.
When p2–p3 is present, those three vertices form the exceptional
triangle.

This characterizes the residual cut obstruction rather than assuming
the cap is cyclically four-edge-connected. The theorem
`ThetaAsymmetricFaithfulTriangleCuts.only_triangle_shore` does not
supply a factor for the triangle case or settle Kelmans.

Use Lean 4.19.0 and Mathlib at
`c44e0c8ee63ca166450922a373c7409c5d26b00b` on `LEAN_PATH`.
Run `bash kelmans-theta-asymmetric-triangle-cut/replay.sh` from the repository root.
