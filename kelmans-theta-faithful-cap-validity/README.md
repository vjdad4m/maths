# Kelmans F2: an exact test for the faithful cap's cut condition

Take the exact cubic seven-wire faithful layout in a cyclically
five-edge-connected ambient graph. The specified three-vertex cap is
cyclically four-edge-connected precisely when the three designated
port groups are independent in the exterior. This removes assumed
cap validity from the smaller-F2 reduction for this layout, replacing
it with five concrete nonedge tests.

Lean checks both directions. A forbidden port edge gives a triangle
in the cap. Conversely, large shores are handled by the
[local cut comparison](../kelmans-theta-faithful-local-cut/) and
tiny shores by exact port incidences and cubic degree counts.

Main theorems: `cap_valid_iff_independent_groups` and
`reduce_of_independent_groups` in namespace
`ThetaSevenFaithfulValid`. These do not assert the port groups are
always independent, or resolve general F2 or Kelmans.

Use Lean 4.19.0 and Mathlib at
`c44e0c8ee63ca166450922a373c7409c5d26b00b` on `LEAN_PATH`.
Run `bash kelmans-theta-faithful-cap-validity/replay.sh` from the repository root.
