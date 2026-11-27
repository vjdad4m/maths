# Graffiti.pc #133: a crossing budget for a nested seven-cycle

Let the graph be four-cycle-free. Suppose an induced base contains
a dominating induced seven-cycle and no induced nine-vertex path.
Every vertex outside the base sees at least one of two designated
base vertices. Other edges into the base are allowed.

Lean proves average local independence at most four in the entire
graph when three times the number of base vertices touching the
cycle in multiple places, plus twice the number of edges into the
base's nondesignated vertices, is at most 14. In particular, up to
two multiple-contact vertices and four additional crossing edges
are allowed. There is no radius hypothesis and no induced-path
restriction on the entire graph.

The proof transports the signed excess over mean four across a
pure two-gate layer without increasing it, then pays at most two
units for each restored crossing. The general nested and #133 cases
remain open.

Use Lean 4.19.0 and Mathlib at
`c44e0c8ee63ca166450922a373c7409c5d26b00b` on `LEAN_PATH`.
Run `bash graffiti-133-nested-c7-crossing-budget/replay.sh` from the repository root.
