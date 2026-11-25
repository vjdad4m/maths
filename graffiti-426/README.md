# Graffiti.pc #426

[Graffiti.pc catalogue](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/), with the [exact statements](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json) and [definitions](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/definitions.json).

Notation: all graphs are finite, undirected, and simple. For a set U, N(U) is the union of its open neighborhoods, and G[U] is its induced subgraph. A total dominating set D requires every vertex, including each member of D, to have a neighbor in D. Write γ_t for its minimum size. A support is a neighbor of a graph leaf.

## #426: independent domination and the neighborhood of max-degree vertices (proved)

**Claim.** If G is connected on n>3 vertices and M is its max-degree set, then i(G) ≤ n−γ(G[N(M)]), where i is independent domination and γ is ordinary domination.

**Proof.** Put U=N(M) and W=M∖U. The set W is independent. Every isolated vertex z of G[U] has a neighbor m in M by z∈U, and then m∉U since z is isolated there; hence m∈W. Extend W to a maximal independent set I of G, which is a dominating set. No isolate of G[U] lies in I. Every vertex in I∩U thus has a neighbor in U, and that neighbor is outside I by independence. Therefore U∖I dominates G[U]; adding both upper bounds yields i(G)+γ(G[U])≤|I|+|U∖I|≤n. The argument works for arbitrary choices of M.

## Verification scope

This is a written proof, not a full Lean formalization.

AI-assisted work shared for review. No priority claim is made.
