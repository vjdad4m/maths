# Graffiti.pc #199 — one-omission path flanks

Start with a simple path through every vertex except `z` in a
nontraceable graph. An omitted neighbor is a neighbor of `z` on
that path. Every omitted neighbor has a predecessor and successor
and neither is another omitted neighbor.

The predecessor chord splice reverses the block between two chosen
predecessors, joins them by the chord, and inserts `z` before the
second omitted neighbor. A chord from the terminal vertex to a
predecessor also permits insertion after a suffix rotation.
Consequently the right endpoint and all predecessors form an
independent set of size `degree(z) + 1`. Adding `z` increases its
size by one. Reversing the path gives the corresponding successor
statement.

For any independent set `A` within the omitted neighborhood, let
`B` be the terminal vertex and predecessor vertices with exactly
one neighbor in `A`. When the largest induced tree has order at
most five, the checked inequality is `|A| + |B| ≤ 4`. Otherwise
`z`, `A`, and `B` form a larger induced tree. In particular, with
a cubic omission, at least two of the four terminal flanks agree
on their contacts to any two nonadjacent omitted neighbors.
The no-independent-six case also forces the initial endpoint to
equal or see a predecessor that is not a successor of any omitted
neighbor.

For three independent omitted neighbors, if a cubic mate is not
penultimate and the next omitted neighbor is farther than two path
edges away, the predecessor of the mate sees another omitted
neighbor. The statement works in either orientation. For the compact
placement

    P — A — X — B — Y — C — Q

with `A,B,C` independent neighbors of `z` and at least one cubic
vertex among them, the graph induced on the seven labels and `z`
has one of six adjacency rows. The weights of the optional edges
`PB, PC, PQ, XC, AY, AQ, BQ` are `1,2,4,8,16,32,64`.
The surviving masks are `38,46,54,62,79,117`. The other rows with a
cubic slot have explicit six-vertex induced-tree certificates, checked
by Lean. In all six rows `PQ` is an edge, and neither end of the block
can be an endpoint of the full path.

`minimum_cubic_edge_flank_profile` connects the flank and endpoint
theorems to the minimum-order contraction argument in the archived
cut case. Its omitted cubic endpoint admits a one-omission path and
every such path satisfies the stated profile. The position and compact
row theorems give additional restrictions when the independent
neighbor and placement hypotheses hold. The surviving patterns still
need a spanning-path reroute or another obstruction to close the case.

The previous #199 one-omission theorem supplies the insertion
constraints and the minimum-order hypothesis. The archived #189
rotation proof is formulated for a longest Mathlib walk. These
splices preserve a list of vertices and apply to any path with
exactly one omission. The published #199 `PathOn.rev` and three-neighbor
exhaustion lemmas are reused directly.

- [Previous one-omission reduction](https://github.com/vjdad4m/maths/blob/main/graffiti-199-cubic-contraction/OmissionObstruction.lean)
- [Path reversal](https://github.com/vjdad4m/maths/blob/main/graffiti-199-separated-four-blocks/src/PairedEntries.lean)

## Strict replay

Use Lean 4.19.0 and Mathlib at
`c44e0c8ee63ca166450922a373c7409c5d26b00b`. From the repository root,
set `GRAFF199_MATHLIB` to the local Mathlib checkout and run:

    bash graffiti-199-cubic-flanks/replay.sh --from-source "$PWD"

The script checks dependency source hashes and compiles the modules
with warnings as errors.
