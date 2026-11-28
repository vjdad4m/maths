# Graffiti.pc #384b: diversity eleven reduces to 10–13 nonisolated vertices

For a finite simple graph, let the diversity be the number of distinct
vertex triangle counts. At diversity eleven the conjectured 2-domination
bound is the graph order minus six. The supported nine-high case is now
proved when there are at least fourteen nonisolated vertices, with no
connectivity restriction. Together with the verified upper case, any
counterexample at diversity eleven has a spanning triangle-supported
counterexample preserving all its vertex triangle counts, with exactly
nine high vertices (degree at least three) and between ten and thirteen
nonisolated vertices.

The proof is analytic. In a failing supported lower profile, adjacent low
vertices either give an isolated low triangle or share a high anchor.
The isolated component yields an odd positive palette piece, giving the
extra omission. Two distinct pendant pairs contradict the previously
verified footprint deficit bound. If five independent low vertices may
be omitted and at least three are ordinary ears, double counting proves
that one ordinary ear has two private high anchors. Restore that one
ear and omit both anchors. Each anchor still has a second kept neighbor
because its degree is at least three. In the four-omission pendant case,
the omitted lows touch at most seven high vertices; omit two previously
untouched high vertices as well.

Main declarations:
- `Graffiti384b.DiversityEleven.exact_large_lower_profile`
  (`LargeLowerProfile384b.lean`).
- `Graffiti384b.DiversityEleven.residual_eleven`
  (`DiversityElevenResidual384b.lean`).

This does not settle diversity eleven or general #384b. No numerical
enumeration is part of these proofs.

## Replay

Use Lean 4.19.0 (6caaee842e94) and Mathlib v4.19.0
(c44e0c8ee63ca166450922a373c7409c5d26b00b). Put the earlier
diversity-eleven-structure, diversity-eleven-lower, and
diversity-eleven-upper object directories and their transitive
prerequisites on `LEAN_PATH`. Run `lake env bash /path/to/this/package/replay.sh`.
The allowed axiom audit is `propext`, `Classical.choice`, and `Quot.sound`.
