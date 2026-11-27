# Kelmans: six one-cap routes fail on a fixture that admits a three-cap lift

For the exact cubic 16-vertex theta fixture of the
[faithful three-cap reduction](../kelmans-theta-faithful-threecap/),
Lean checks that all six previously considered incident one-vertex
cap choices have an explicit triangle. They fail the required
cyclic-four cut condition. The actual target still has a checked
factor obtained through the faithful three-cap route.

This is a limitation of those six cap constructions, not a
counterexample to F2 or Kelmans. This source does not assert that the
original 16-vertex fixture is cyclically five-edge-connected.
Exact theorem: `ThetaSevenFaithfulFailedOneCaps.all_six_incident_onecaps_fail`.

Use Lean 4.19.0 and Mathlib at
`c44e0c8ee63ca166450922a373c7409c5d26b00b` on `LEAN_PATH`.
Run `bash kelmans-theta-six-onecap-obstruction/replay.sh` from the repository root.
