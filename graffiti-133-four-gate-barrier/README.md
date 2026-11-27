# Graffiti.pc #133: a four-gate signed-score obstruction

Lean checks a 12-vertex graph with no four-cycle and no induced
nine-vertex path. Its base consists of four independent gates. Each
exterior vertex has exactly one base neighbor. Adding the exterior
increases the signed score, the sum of local independence numbers
minus four times the order, by exactly two.

This is an obstruction to a zero-gain rule for four gates, not a
counterexample to Graffiti.pc #133: the full graph still has negative
signed score. The checked predicates include the induced-path absence
and exact graph counts.

Use Lean 4.19.0 and Mathlib at
`c44e0c8ee63ca166450922a373c7409c5d26b00b` on `LEAN_PATH`.
Run `bash graffiti-133-four-gate-barrier/replay.sh` from the repository root.
The finite no-path proof can take a few minutes.
