# Graffiti.pc #310

[Graffiti.pc catalogue](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/), with the [exact statements](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json) and [definitions](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/definitions.json).

Notation: all graphs are finite, undirected, and simple. For a set U, N(U) is the union of its open neighborhoods, and G[U] is its induced subgraph. A total dominating set D requires every vertex, including each member of D, to have a neighbor in D. Write γ_t for its minimum size. A support is a neighbor of a graph leaf.

## #310: minimum total distance (proved)

**Claim.** If G is connected and n>2, then γ_t(G) ≤ ceil(1 + τ/3), where τ = min_r Σ_v dist_G(r,v).

**Proof.** Let r attain τ, and use a breadth-first tree rooted at r. If the tree is a star rooted at its hub, r is universal in G, so γ_t(G)=2 and τ=n−1≥2. Otherwise all internal vertices of the rooted tree form a total dominating set: r has a child that is internal, and every other vertex has an internal parent. Let I be the number of nonroot internal vertices. For each nonroot internal vertex v choose a child c(v). These children are all distinct and have depth at least 2. If v has depth at least 2, charge 3 to its chosen child, which has depth at least 3. If v has depth 1, charge 1 to v and 2 to its chosen child. All spending is within the charged vertex’s depth, without reuse. Thus 3I ≤ τ, and γ_t(G) ≤ 1+I ≤ 1+floor(τ/3).

## Verification scope

This is a written proof, not a full Lean formalization.

AI-assisted work shared for review. No priority claim is made.
