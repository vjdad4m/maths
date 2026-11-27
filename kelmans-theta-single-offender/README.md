# Kelmans F2: the singly offending contact edge

This is a conditional result for the specified seven-vertex theta attachment.
The graph is cubic, has the stated cyclic-four and cyclic-five cut properties,
has order four modulo six, and has five distinct exterior contact vertices.
If the prescribed exterior edge to omit is one of the two opposite contact
pairs and the other pair is nonadjacent, Lean proves the factor after root
deletion under the explicit `HittingAvoidance` premise.

The proof shows that any nontrivial cut of size at most three in the path cap
must separate off exactly a leaf triangle. The actual omitted edge and the
midpoint wire lie on opposite shores in every such cut. This is the precise
condition required by the earlier [hitting-handle approach](../kelmans-single-cut/).
After applying the avoidance premise, the
[blocked-cap transfer](../kelmans-theta-exterior-avoidance/) constructs the
factor in the original graph with only the requested exterior edge omitted.

The main theorem is `ThetaFiveSingleOffender.singly_offending_exterior_omission`.
The hitting-avoidance premise is explicit in this release. Avoiding a different
exterior edge while a contact pair is adjacent, and the case of both pairs
adjacent, are not covered here. General Kelmans/F2 remains open.

Use Lean 4.19.0 and Mathlib at `c44e0c8ee63ca166450922a373c7409c5d26b00b`
on `LEAN_PATH`, then run `bash kelmans-theta-single-offender/replay.sh`.
