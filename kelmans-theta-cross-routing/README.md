# Kelmans F2: cross-routing when both default replacement pairs are adjacent

This is a conditional reduction for the exact seven-vertex theta
attachment in a finite cubic graph of order four modulo six, under the
stated cyclic-four and cyclic-five cut hypotheses. Exactly one original
opposite contact pair is adjacent. After absorbing it, suppose both
default replacement pairs are adjacent and neither edge is the requested
exterior omission. The omission is also different from the absorbed edge.

Pair the two old live contacts together and the two new contacts
together. Both new cap pairs are nonadjacent: one by the original
hypothesis, the other because an adjacency would give a 4-cycle.
Square-freeness of the exterior is derived, not assumed separately.
The resulting cap is cyclically four-edge-connected, 3-connected, and
six vertices smaller. Under smaller-order cyclic-four F2, its exact
omission can be lifted to the original theta. This includes edges
represented by a cap wire. The nine two-leaf modes are certified.

The two exact orientations are
`ThetaCrossEarOriginal.original_from_adjacent` and
`ThetaCrossEarMirror.mirrored_original_from_adjacent`.
This handles the situation where the
[default prescribed cap can fail](../kelmans-theta-adjacent-ear/).
It does not cover only one default replacement edge, omitting a
required edge, or general F2/Kelmans.

Use Lean 4.19.0 and Mathlib at `c44e0c8ee63ca166450922a373c7409c5d26b00b`
on `LEAN_PATH`, then run `bash kelmans-theta-cross-routing/replay.sh`
from the repository root.
