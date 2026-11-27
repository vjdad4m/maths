# Kelmans F2: a root-contact cap for incident theta omissions

For an exact cubic seven-theta attachment of order four modulo six,
suppose the specified exterior edge touches a live terminal. If the
terminal and the root contact can be joined without a repeated edge
and the precise one-vertex cap is cyclically four-edge-connected,
the target reduces to smaller cyclic-four F2, on six fewer vertices.

Deleting the selected terminal suppresses both the artificial edge
and the requested genuine edge. The cap omission is used on its
opposite wire. A factor of the resulting cap lifts without ever
restoring the specified edge. This gives an F2-only route under
the stated cap condition, with no order-zero avoidance premise.

The precise result is `ThetaRootContactCap.incident_exterior`. The
package also verifies a concrete 16-vertex no-opposite-edge example:
a checked factor of the ten-vertex cap lifts to the original
instance with edge 7–12 omitted. This does not show every no-ear
configuration admits the cap.

Replay with Lean 4.19.0 and Mathlib at
`c44e0c8ee63ca166450922a373c7409c5d26b00b` on `LEAN_PATH`:
`bash kelmans-theta-root-contact-cap/replay.sh`.
