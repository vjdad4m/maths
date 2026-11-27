# Kelmans P₃-factor problem: adjacent contacts in the theta reduction

This is a conditional reduction for the strengthened vertex-and-edge-deletion
statement, not a solution of the Kelmans conjecture. The theorem
`EarReducesTheta.original_either_adjacent_pair_reduces` begins with the
original seven-vertex theta attachment, its specified two internal triples,
and the stated cyclic-five cut and no-four-cycle hypotheses. If either of
the two exterior contact pairs obstructs the earlier routing by being
adjacent, the theorem reduces this case to the strengthened cyclic-four
statement on a graph with six fewer vertices.

The construction absorbs the offending adjacent pair into the attachment.
The exact cyclic-five cut condition ensures that the new external contacts
are distinct. The new cap is cubic and 3-connected, satisfies the cyclic-four
cut condition, and has the right order modulo six. A factor from the
smaller-order hypothesis gives a forced three-vertex path that can be
translated back, restoring the two original triples. The ambient proof
does not assume the cap is cyclic-five.

The cap geometry uses the five-edge cap of Máčajová and Rajník,
[*Decomposition of cubic graphs with cyclic connectivity 5*](https://arxiv.org/abs/2107.09756).
The smaller-order hypothesis is essential to this theorem and is not proved
by this package.

To replay, use Lean 4.19.0 with Mathlib at
`c44e0c8ee63ca166450922a373c7409c5d26b00b` and an existing Mathlib
`LEAN_PATH`. Run `bash kelmans-theta-ear-reduction/replay.sh` from the
repository root.
