# Graffiti.pc #133: bounded multiple contacts with a dominating seven-cycle

Let a finite simple graph have no four-cycle, no induced nine-vertex
path, and a dominating induced seven-cycle. A vertex outside the cycle
is a multiple-contact vertex if it sees at least two cycle vertices.

Lean proves that average local independence is at most four whenever
the sum of ambient degrees of the multiple-contact vertices is at
most twice their number plus seven. In particular it proves the bound
if at most two vertices have multiple contacts, or if all such
vertices have three contacts. No hypothesis restricts exterior
triangles or radius in these conclusions.

The argument strengthens the single-contact theorem by 14 units of
slack in the total local-independence bound. Deleting the extra
vertices preserves the single-contact hypotheses and charges at most
twice their ambient degree per vertex. Geometry bounds the degree
and number of triple-contact vertices. The main lemmas are
`mean_four_of_multi_degree_budget`, `at_most_two_multi_vertices_mean_four`,
and `all_multis_triple_mean_four` in namespace `Graffiti133MultiC7`.
The general conjecture remains open.

Use Lean 4.19.0 and Mathlib at
`c44e0c8ee63ca166450922a373c7409c5d26b00b` on `LEAN_PATH`.
Run `bash graffiti-133-multiple-contact-small-scopes/replay.sh` from the
repository root.
