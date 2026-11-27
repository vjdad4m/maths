# Graffiti.pc #199 compact omission

## Checked scope

**Graffiti199Depleted.CompactOmission.traceable_of_compact_cubic_omission** proves the graph is traceable if its induced-tree number is at most five and a path through all vertices except a cubic vertex z visits its three independent neighbors A, B, C in a consecutive block P,A,X,B,Y,C,Q. One of A, B, C must also have degree three. The theorem permits arbitrary lengths of the two exterior path flanks. It requires no connectivity or independence-number hypothesis.

**Graffiti199Depleted.CompactOmission.no_compact_placement** takes a cubic neighbor of z instead of naming the cubic slot; the proof places that neighbor in the block using the three distinct neighbors of z.

**Graffiti199Depleted.ContractedEdge.minimum_cubic_edge_noncompact_omission** applies the exclusion to the endpoint omission guaranteed by the previously checked cubic-edge contraction. Its hypotheses are strict minimum order among connectivity-at-least-three counterexamples, connectivity at least three, the archived crossing condition on surviving edges, induced-tree number at most five, graph order at least ten, and the two cubic degrees. On every one-omission path with the selected omission, the compact placement with independent neighbors is impossible. Wider gaps, other omitted-neighborhood shapes, and the general conjecture remain open in this lane.

**Graffiti199Depleted.CompactOmission.two_intervening_vertices** puts the exclusion in terms of gaps. If a nontraceable graph with the same tree bound has a cubic omission with independent neighbors and a cubic neighbor, then on any spanning path of its deletion, at least one of the two gaps between successive visits to the omitted vertex's neighbors has at least two intervening vertices.

## Proof

The published compact classification reduces the eight core vertices to six possible adjacency rows and forces P–Q. The single-vertex table checks every possible contact profile of an exterior vertex for each row, using the two cubic degrees to rule out contact with the omission and its cubic neighbor.

The two-vertex table studies the two exterior vertices closest to the block. Each case gives a six-vertex induced tree, a spanning splice through the eight core vertices, or equal contact profiles for the two exterior vertices with an edge between them. The surviving profile meets Q in every row.

Hold the right exterior vertex fixed. The next-vertex table checks each extra vertex immediately to the left of the processed left flank. A route through the block uses the processed left vertex next to an endpoint of the route, so the whole processed flank can replace that vertex. In the remaining case the next vertex has the same profile and sees the fixed right vertex. Induction along the whole left flank then forces the first vertex of the path to see Q, a successor of a neighbor of the omission. This contradicts the terminal-flank lemma for the reversed path.

The three finite tables give explicit six-tree orders and path orders. Lean checks every input using ordinary kernel reduction. The embedding and path-replacement lemmas transport the checked orders into the original graph.

## Reuse and replay

The primary baseline is [the published cubic-flank package](https://github.com/vjdad4m/maths/tree/main/graffiti-199-cubic-flanks). The proof imports its compact-row classification, terminal-flank independence, and omission-permutation bridge. The minimum-order adapter uses its transitive [cubic-contraction package](https://github.com/vjdad4m/maths/tree/main/graffiti-199-cubic-contraction).

Use Lean 4.19.0 and Mathlib at
`c44e0c8ee63ca166450922a373c7409c5d26b00b`. From the repository root,
set `GRAFF199_MATHLIB` to the local Mathlib checkout and run:

    bash graffiti-199-cubic-compact-closure/replay.sh --from-source "$PWD"

The ordered manifests pin the dependency and new source hashes. The
scope theorems use only `propext`, `Classical.choice` and `Quot.sound`.
