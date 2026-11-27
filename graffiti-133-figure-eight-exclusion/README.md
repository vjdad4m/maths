# Graffiti.pc #133: excluding a figure-eight exterior witness

Lean proves that a graph with no ordinary 4-cycle and no induced
nine-vertex path cannot contain this configuration: an induced 7-cycle,
together with an induced subgraph outside it that is triangle-free and
has one vertex of degree four and all other vertices of degree two.
Every vertex in that subgraph must have exactly one neighbor on the
7-cycle for the theorem to apply.

The component through the degree-four vertex is formed by two cycles
sharing that vertex. The absence of a long induced path restricts the
cycle lengths to 5+5 or 5+6. The checked witnesses from the
[19-motif result](../graffiti-133-bicycle-motifs/) then produce the
forbidden induced path in the whole graph.

The main theorem is
`Graffiti133Bicycle.no_single_branch_bicycle_of_singleton_seven`.
It excludes the one-degree-four branch only. The alternative with two
degree-three vertices and the general conjecture are not settled here.

Use Lean 4.19.0 and Mathlib at `c44e0c8ee63ca166450922a373c7409c5d26b00b`
on `LEAN_PATH`. Run `bash graffiti-133-figure-eight-exclusion/replay.sh`
from the repository root.
