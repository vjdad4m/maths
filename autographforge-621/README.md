# AutoGraphForge normalized line 621

**Proved in Lean.** For every finite claw-free subcubic graph, the
vertex clique-partition number is at most the Roman domination number.
This is the exact [pinned row](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L621)
(ID `0ec32efb`).

The proof applies to every quasi-line graph and, in particular, every
claw-free graph of maximum degree at most four. In a Roman labeling,
assign each zero-labeled vertex to an adjacent defender labeled two.
The defender and its assigned vertices can be partitioned into at most
two cliques because its neighborhood is covered by two cliques.
Each vertex labeled one uses one part, so the total does not exceed
the Roman weight.

The degree threshold in the claw-free extension is sharp: the wheel
with a five-vertex rim is claw-free of maximum degree five and has
clique-partition number three and Roman domination number two.
The exact claims are checked in `QuasiLineRoman.lean`.

Use Lean 4.19.0 and Mathlib at `c44e0c8ee63ca166450922a373c7409c5d26b00b`,
then run `MATHLIB_DIR=/path/to/mathlib4 bash autographforge-621/replay.sh`.
