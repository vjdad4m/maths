# Kelmans: a local cut comparison for the faithful cap

In the normalized seven-wire layout of the
[faithful three-cap route](../kelmans-theta-faithful-threecap/),
fix arbitrary two-color assignments on the five original exterior
contacts and three cap vertices. Lean proves that the five exterior
colors extend to the nine original patch vertices with at most one
more local crossing edge than the cap has.

The theorem `ThetaSevenFaithfulLocalCut.local_cut_domination`
counts the actual listed wire incidences. It is a local comparison;
it does not assert a full ambient graph cut identity or that the
faithful cap is always cyclically four-edge-connected.

Use Lean 4.19.0 and Mathlib at
`c44e0c8ee63ca166450922a373c7409c5d26b00b` on `LEAN_PATH`.
Run `bash kelmans-theta-faithful-local-cut/replay.sh` from the repository root.
