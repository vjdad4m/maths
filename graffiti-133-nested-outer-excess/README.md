# Graffiti.pc #133: two exterior regions with positive edge excess force a long path

In a finite four-cycle-free graph, take two disjoint exterior regions
with no edges between them and at most five designated gate vertices.
Every vertex of the regions sees exactly one gate, and adjacent region
vertices have different designated gates. Assume the union of the
regions is triangle-free.

If each induced region has more edges than vertices, the graph
contains an induced path on nine vertices. In a graph without such a
path, therefore, at most one such exterior component can have
positive edge excess.

The proof extracts a minimal positive-excess subregion. Its minimum
degree is at least two and one vertex has at least three neighbors.
The resulting induced four-vertex arms can start at three gate
colors, so two regions share a usable gate and assemble the path.

Main theorem: `Graffiti133NestedFour.P9_of_two_outer_edge_excesses`.
The result does not bound excess in the one remaining component or
settle the general conjecture.

Use Lean 4.19.0 and Mathlib at
`c44e0c8ee63ca166450922a373c7409c5d26b00b` on `LEAN_PATH`.
From repository root run `bash graffiti-133-nested-outer-excess/replay.sh`.
