# Graffiti.pc #361

[Graffiti.pc catalogue](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/), with the [exact statements](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json) and [definitions](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/definitions.json).

Notation: all graphs are finite, undirected, and simple. For a set U, N(U) is the union of its open neighborhoods, and G[U] is its induced subgraph. A total dominating set D requires every vertex, including each member of D, to have a neighbor in D. Write γ_t for its minimum size. A support is a neighbor of a graph leaf.

## #361: isolated supports and centers (proved)

**Claim.** For a tree T on n>2 vertices with supports S and center set C, γ_t(T) ≥ isolates(T[S])+|C|.

**Proof.** Every support belongs to every total dominating set, since its leaf has no other neighbor. Write k=isolates(T[S]), and choose a minimum total dominating set D. A tree has one or two centers. If T[S] contains an edge then |S|≥k+2, so we are done. Otherwise S is independent and k=|S|. At least one vertex outside S belongs to D to dominate S, and two suffice for the inequality. If exactly one y does, each support is adjacent to y. All remaining vertices have a neighbor in S∪{y}. The star with center y and other vertices S, together with one such edge per remaining vertex, already spans a tree. Hence these are all the edges, and each remaining vertex is a leaf. None can attach to y, since y is not a support. If |S|=1, T is a star, with a unique center. If |S|≥2 each support has at least one leaf and each branch at y has length 2, so y is the unique center. In both cases |D|=k+1 proves the claim.

## Verification scope

This is a written proof, not a full Lean formalization.

AI-assisted work shared for review. No priority claim is made.
