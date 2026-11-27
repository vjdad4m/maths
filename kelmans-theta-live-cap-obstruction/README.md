# Kelmans: a method obstruction for four live-to-live theta caps

Lean checks a cubic, 3-connected, cyclically 5-edge-connected
16-vertex exact theta fixture with both original opposite contact
edges absent. Each of the four one-vertex completions obtained
by joining two nonopposite live contacts contains a triangle and
fails the required smaller cap condition.

This is an obstruction to that particular construction only. The
actual target graph after deleting root 6 and omitting edge 10–14
has an explicit checked factor. Root-to-live, opposite-live, and
other cap constructions are not ruled out.

See `ThetaNoEarOneCapFixture.four_caps_all_fail` and
`ThetaNoEarOneCapFixture.target_has_factor`. Replay with Lean 4.19.0
and Mathlib at `c44e0c8ee63ca166450922a373c7409c5d26b00b`:
`bash kelmans-theta-live-cap-obstruction/replay.sh`.
