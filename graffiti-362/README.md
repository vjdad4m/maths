# Graffiti.pc #362

[Graffiti.pc catalogue](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/), with the [exact statements](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json) and [definitions](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/definitions.json).

Notation: all graphs are finite, undirected, and simple. For a set U, N(U) is the union of its open neighborhoods, and G[U] is its induced subgraph. A total dominating set D requires every vertex, including each member of D, to have a neighbor in D. Write γ_t for its minimum size. A support is a neighbor of a graph leaf.

## #362: support components and radius (proved)

**Claim.** For a tree T on n>2 vertices with supports S and leaves L, γ_t(T) ≥ c(T[S∪L])+(1+rad(T))/3.

**Proof.** Each leaf in T[S∪L] attaches to a support, and no two leaves are adjacent, so c(T[S∪L])=c(T[S]). From a minimum total dominating set D, reserve one support per component of T[S]; call the reserved set R. This is an independent set contained in D. Each vertex has a neighbor in D, and a neighbor in R in turn has a neighbor in D∖R. Therefore D∖R dominates every vertex within distance 2. Any vertex can cover at most five vertices of a fixed path within distance 2: two covered vertices are at distance at most 4, and path distance equals tree distance. On a diametral path, |D∖R| ≥ ceil((diam(T)+1)/5). For r=rad(T), diam(T)≥2r−1, so this is at least ceil(2r/5)≥(r+1)/3. The last comparison holds without rounding for r≥5 and is direct for r=1,2,3,4. Add |R|.

## Verification scope

This is a written proof, not a full Lean formalization.

AI-assisted work shared for review. No priority claim is made.
