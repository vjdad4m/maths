# Graffiti.pc #133: nineteen configurations forcing an induced nine-vertex path

This partial result applies to a graph with no ordinary 4-cycle. Suppose it
contains an induced 7-cycle and one of the 19 listed induced configurations
outside that cycle, with exactly one neighbor on the cycle for each vertex of
the configuration. Lean checks that the full graph contains an induced path on
nine vertices, allowing every assignment of the cycle neighbors.

The configurations are sixteen theta graphs (three internally disjoint paths
with common ends) and three pairs of cycles joined by a path, including the
shared-vertex case. The lengths that specify them are in
`src/BicycleKeys133.lean`. A finite certificate exhausts the possible
attachments. Each surviving search branch supplies an explicit induced path;
the Lean verifier checks the witness and transfers it to the original graph.
The Python generator is not trusted by the theorem. Canonical adjacency
labeling for the 19 certificates is independently checked in
`BicycleShapeCatalog133.lean`.

This does not prove that every exterior of an induced 7-cycle must have one of
these configurations, and it does not resolve #133. To replay, use Lean 4.19.0
and Mathlib at `c44e0c8ee63ca166450922a373c7409c5d26b00b` with Mathlib
on the existing `LEAN_PATH`, then run `bash graffiti-133-bicycle-motifs/replay.sh`
from the repository root. Python 3 generates the 19 certificate modules.
