# Kelmans F2: one default replacement edge at a theta ear

In the exact cyclic-four/cyclic-five cubic theta setting of order
four modulo six, suppose one original opposite contact pair is adjacent.
After absorbing it, assume exactly one of the two default replacement
pairs is adjacent. Every genuine requested exterior omission other
than the absorbed edge can be realized assuming smaller-order
cyclic-four F2. In particular, the omission may be the sole existing
default replacement edge. The other original opposite pair need not
be nonadjacent.

Use the surviving cap leaf for the nonadjacent replacement pair, and
choose the deleted leaf’s contacts so that its connection to the
original root does not use an edge already present. The cap is
three-vertex-connected and six vertices smaller. The six refill
modes retain the absorbed edge, but do not use the sole existing
replacement edge. Symmetry handles both choices and both orientations.

See `ThetaDeadLeafSymmetry.only_one` and
`ThetaDeadLeafSymmetry.reflected_only_one`. This is a conditional
reduction, not a proof of F2 or the Kelmans conjecture.

Use Lean 4.19.0 and Mathlib at
`c44e0c8ee63ca166450922a373c7409c5d26b00b` on `LEAN_PATH` and run
`bash kelmans-theta-single-extra/replay.sh` from the repository root.
