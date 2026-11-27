# Graffiti.pc #133: a three-gate crossing budget

In a finite four-cycle-free graph, consider an induced base with
no induced nine-vertex path and a dominating induced seven-cycle.
Suppose every exterior vertex has a neighbor at one of three
designated base vertices. Edges to those three vertices are allowed
without a numerical cap.

The full graph has average local independence at most four if
three times the number of base vertices touching the cycle more than
once, plus twice the number of edges from outside to the base's
nongate vertices, is at most 12. No radius or induced-path
hypothesis on the full graph is required.

The core lemma bounds the increase in signed excess over mean four
by twice the number of exterior vertices touching all three gates
when no nongate crossings are present. Ordinary four-cycle-freeness
limits the latter count to one. The crossing budget pays separately
for the restored nongate edges. The general #133 remains open.

Use Lean 4.19.0 and Mathlib at
`c44e0c8ee63ca166450922a373c7409c5d26b00b` on `LEAN_PATH`.
Run `bash graffiti-133-nested-c7-three-gate/replay.sh` from the repository root.
