# Graffiti.pc #133: a dominating induced seven-cycle without an induced eight-vertex path

Let the finite simple graph contain no four-cycle and no induced
eight-vertex path. If an induced seven-cycle dominates the whole
graph, average local independence is at most four. This requires
no radius assumption and allows arbitrary exterior contacts and
triangles.

The [weighted insertion argument](../graffiti-133-dominating-c7-radius-four/)
is combined with two bounds. An adjacent contact pair with three
exterior neighbors forces an additional triangle when there is no
induced eight-vertex path, reducing its charge. A finite check of
three-profile obstructions bounds the total charge by the available
14 units of slack.

Main theorem: `Graffiti133MultiP8.P8_free_dominating_C7_mean_four`.
Domination of only a proper core does not suffice for this statement.
The general conjecture remains open.

Use Lean 4.19.0 and Mathlib at
`c44e0c8ee63ca166450922a373c7409c5d26b00b` on `LEAN_PATH`.
Run `bash graffiti-133-dominating-c7-path-eight-free/replay.sh` from the repository root.
