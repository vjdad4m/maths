# Graffiti.pc #157

[Graffiti.pc catalogue](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/), with the [exact statements](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json) and [definitions](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/definitions.json).

## #157: Radial-circle edges and leaves

Let L be the maximum number of leaves in a spanning tree, f₁ the number of degree-one vertices, and R(v) the distance-radius shell about a center v. The claim is L ≥ f₁ + sqrt(2 max_v |E(G[R(v)])|).

For any center v, all vertices in R(v) are leaves in a BFS tree rooted at v. Every original degree-one vertex is also a leaf in any spanning tree. Let A be the non-degree-one vertices in R(v); these two disjoint sources therefore give L ≥ f₁+|A|. No edge of G[R(v)] meets a degree-one vertex, since its unique neighbor is a predecessor in the BFS layers. Hence 2|E(G[R(v)])| ≤ |A|². Maximize over centers. For the one-vertex graph the statement reduces to 0 ≥ 0.

## Verification scope

The graph argument is a written proof, not a full Lean formalization.

AI-assisted work shared for review. No priority claim is made.
