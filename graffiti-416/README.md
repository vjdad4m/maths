# Graffiti.pc #416

[Graffiti.pc catalogue](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/), with the [exact statements](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json) and [definitions](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/definitions.json).

Notation: all graphs are finite, undirected, and simple. For a set U, N(U) is the union of its open neighborhoods, and G[U] is its induced subgraph. A total dominating set D requires every vertex, including each member of D, to have a neighbor in D. Write γ_t for its minimum size. A support is a neighbor of a graph leaf.

## #416: critical independent sets and pendants (proved)

**Claim.** Let G be connected on n>2 vertices with diameter at most 2, P its pendants, and H the union of all maximum-cardinality critical independent sets (a critical set maximizes |I|−|N(I)| among independent sets). Then |H| ≥ isolates(G[N(N(P))])−2.

**Proof.** If P is empty the right side is −2. Otherwise a pendant p has a unique neighbor u, and the diameter condition makes u universal. All pendants therefore have neighbor u, and N(N(P))=V∖{u}, whose induced isolates are exactly the pendants. If |P|≤2 the inequality is immediate. Otherwise P achieves objective value |P|−1≥2. A critical independent set I is therefore nonempty and cannot contain u: the only independent set containing u is {u}, with objective value 2−n. Now u∈N(I); if a pendant p were missing from I, adding it preserves independence and adds no neighbor, increasing the objective. Thus P⊆I⊆H.

## Verification scope

This is a written proof, not a full Lean formalization.

AI-assisted work shared for review. No priority claim is made.
