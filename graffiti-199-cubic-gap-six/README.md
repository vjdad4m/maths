# Graffiti.pc #199 wider one-omission placements

## Scope

Let G be a finite simple graph with induced-tree number at most five. Let z be a cubic vertex with a cubic neighbor. Suppose a path covers every vertex except z, and the three neighbors of z are independent. The new Lean theorems force a Hamiltonian path whenever the two gaps between consecutive visits to these neighbors have edge lengths 2 and 3, 2 and 4, or 3 and 3. Both orders are covered.

- Placement23.lean defines Graffiti199Depleted.WiderOmission.traceable_of_gaps_two_three and traceable_of_gaps_three_two.
- Placement24.lean defines Graffiti199Depleted.WiderOmission.traceable_of_gaps_two_four and traceable_of_gaps_four_two.
- Placement33.lean defines Graffiti199Depleted.WiderOmission.traceable_of_gaps_three_three.
- GapBounds.lean defines Graffiti199Depleted.WiderOmission.sum_intervening_at_least_five. In the nontraceable case the two gaps together have at least five intervening vertices, hence at least seven edges.
- GapBounds.lean also defines Graffiti199Depleted.ContractedEdge.minimum_cubic_edge_wider_gaps. It produces the endpoint omission in the archived cubic-contraction reduction and imposes the gap bound on every path for that omission with independent omitted neighbors. The adapter uses the archived smaller-order, connectivity-at-least-three, surviving-edge crossing, and graph-order hypotheses.

Wider pairs with at least seven edges in total, other omitted-neighborhood shapes, and the general conjecture remain open in this lane.

## Proof and prior modules

The exact path position supplies the predecessor and successor independent sets for the core. The cubic degrees fix the neighbor lists of the omitted vertex and its cubic neighbor. For each possible cubic neighbor, the finite certificate partitions the remaining adjacency bits by a decision tree. Its leaves give an induced six-vertex tree, a route that can replace the core in the original path, or one of two explicit core configurations needing exterior attachments. The 3-and-3 case uses only the tree witnesses and replacement routes.

For the 2-and-3 and 2-and-4 cases, the attachment tables classify all exterior profiles for each residual core. When the two nearest exterior vertices yield neither a tree nor a route, they have the same designated profile. In either residual core, the next vertex on the left must have that profile again or permit a reroute or induce a six-vertex tree. The induction uses the same whole-flank splice as the earlier result and reaches the first vertex, contradicting the terminal-flank lemma.

The core and route transfer reuses the published [cubic compact closure](https://github.com/vjdad4m/maths/tree/main/graffiti-199-cubic-compact-closure) and its [cubic flank constraints](https://github.com/vjdad4m/maths/tree/main/graffiti-199-cubic-flanks). The [#189 four-omission splice](https://github.com/vjdad4m/maths/blob/main/graffiti-189-order-thirteen/src/SmallOrderFour189.lean#L1690) requires an edge-optimal walk with degree-four endpoints and four omitted vertices. The #199 endpoint-preserving splice applies directly to a cubic one-omission path.

## Strict replay

Use Lean 4.19.0 and Mathlib at
`c44e0c8ee63ca166450922a373c7409c5d26b00b`. From the repository root,
set `GRAFF199_MATHLIB` to the local Mathlib checkout and run:

    bash graffiti-199-cubic-gap-six/replay.sh --from-source "$PWD"

The exact dependency and local source hashes are checked before
compilation with warnings as errors.
