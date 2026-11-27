# Graffiti.pc #199 — contracting a cubic edge in a minimum counterexample

The archived cut law `CrossingBetweenSurvivingEdges G` says that
deleting at most three vertices cannot separate two surviving edges.
For a graph of order at least ten with connectivity at least three and
induced-tree number at most five, the previous cubic-matching package
proves that an edge between two cubic vertices has no common neighbor
of its endpoints.

The new minimum-order reduction uses the following facts.

1. Contracting an edge with no common neighbor reduces the order by one,
   preserves connectivity at least three under the archived cut law,
   and cannot increase the largest induced-tree order. A small cut in
   the contraction lifts to at most three deleted vertices. If the lift
   deletes three, both ends of the original edge were deleted, so a
   surviving isolated vertex would be a common neighbor. For the tree
   bound, split the contracted vertex into the original edge and lift
   ranks from the unique rooted paths in an induced tree.
2. Minimum order supplies a spanning path in the contraction. The
   checked `smallerAtThree_of_catalogue_minimum` bridge takes the
   exact smaller-graph premise of the catalogue conjecture. It also
   suffices to take minimum order among graphs with connectivity at
   least three and tree number at most five.
3. The contracted vertex cannot be an endpoint of such a spanning
   path. A spanning path through that vertex must enter and leave from
   neighbors of the same original endpoint. The other orientations
   lift to a spanning path of the original graph.
4. Restoring only that endpoint gives a path omitting exactly the
   other cubic endpoint. The omitted vertex has no neighbor at either
   endpoint of this path. No two of its neighbors are consecutive
   along the path, since either circumstance would permit insertion.

The result is `ContractedEdge.minimum_cubic_edge_constrained_omission`.
The conclusion applies to every cubic edge in the stated minimum-order
case, and the earlier `minimum_cubic_contraction_same_side` constrains
every spanning path of each contraction. For a minimum taken only over
the exact-connectivity-three class, `ContractDegree.lean` also proves
that an additional surviving cubic vertex keeps the contraction in that
class and gives `contraction_traceable_of_exact_three_minimum`.

The path produced by the one-omission theorem has free endpoints. The
remaining gap is a rerouting argument for the constrained path, or an
induced six-vertex tree forced by its constraints. The result does not
settle the single cubic component or the full conjecture.

- [Archived cut interface](https://github.com/vjdad4m/maths/blob/main/graffiti-199-four-block-integration/src/RemainingCut.lean)
- [Cubic-edge boundary lemma](https://github.com/vjdad4m/maths/blob/main/graffiti-199-cubic-matching/CubicEdgeCuts.lean)

## Strict replay

Use Lean 4.19.0 and Mathlib at
`c44e0c8ee63ca166450922a373c7409c5d26b00b`. From the repository root,
set `GRAFF199_MATHLIB` to the local Mathlib checkout and run:

    bash graffiti-199-cubic-contraction/replay.sh --from-source "$PWD"

The script checks the pinned dependency source hashes and compiles the
new modules with warnings as errors.
