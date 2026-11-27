# Kelmans F2: omitting an exterior edge at the seven-vertex theta

For the specified seven-vertex theta attachment, assume its ambient graph
is cubic, has the stated cyclic-four and cyclic-five cut properties, has
order four modulo six, and has five distinct exterior contact vertices.
If neither opposite pair (ring sites 1 and 4, and ring sites 2 and 5) is
adjacent in the exterior, the theorem handles **any actual exterior edge**.
Under the explicit cyclic-four two-edge avoidance premise at order zero
modulo six, deleting the theta root and omitting that exterior edge
leaves a graph with a three-vertex-path factor.

The construction replaces the theta by a three-vertex path cap and
suppresses its midpoint's wire to the deleted root's contact, as well as
the prescribed exterior edge. The midpoint's tile either contains both
cap leaves or uses one leaf and one of its contacts. In the latter case
the opposite leaf has three possible tile profiles. Lean checks that all
13 cases reassemble the original six surviving vertices and preserve the
omitted edge. The construction works on the contact-independent fixture
for which the [seven-port cap family fails](../kelmans-seven-port-cap-obstruction/),
subject to the same two-edge avoidance premise.

The theorem is `ThetaFiveExterior.exterior_of_cyclic_two_avoid`.
The two-edge avoidance hypothesis is explicit. The adjacent-contact
branches and general F2/Kelmans are not resolved here.

The path-cap geometry uses Máčajová and Rajník,
[*Decomposition of cubic graphs with cyclic connectivity 5*](https://arxiv.org/abs/2107.09756).
Use Lean 4.19.0 and Mathlib at `c44e0c8ee63ca166450922a373c7409c5d26b00b`
on `LEAN_PATH`, then run `bash kelmans-theta-exterior-avoidance/replay.sh`.
