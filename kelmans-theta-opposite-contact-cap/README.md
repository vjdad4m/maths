# Kelmans F2: an opposite-contact cap for incident theta omissions

For exact cubic seven-theta attachments of order four modulo six,
suppose the specified exterior edge touches a live terminal. Instead
of pairing it artificially with the root contact, pair it with the
opposite live contact (a nonedge in the exterior). Wire a new cap
vertex to the other three contacts. If the resulting cap is
cyclically four-edge-connected, the target reduces to cyclic-four
F2 on six fewer vertices.

Delete the terminal, which suppresses the specified edge and the
artificial edge, and omit the cap wire to the root contact. The
[earlier lifting lemma](../kelmans-theta-root-contact-cap/) reattaches
the deleted terminal only at its original ring wire. Main theorem:
`ThetaOppositePortCap.incident_exterior`. This does not give a
universal cap-existence theorem or settle Kelmans.

Replay with Lean 4.19.0 and Mathlib at
`c44e0c8ee63ca166450922a373c7409c5d26b00b` on `LEAN_PATH`:
`bash kelmans-theta-opposite-contact-cap/replay.sh`.
