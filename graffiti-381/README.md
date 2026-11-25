# Graffiti.pc #381

[Graffiti.pc catalogue](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/), with the [exact statements](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json) and [definitions](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/definitions.json).

Notation: all graphs are finite, undirected, and simple. For a set U, N(U) is the union of its open neighborhoods, and G[U] is its induced subgraph. A total dominating set D requires every vertex, including each member of D, to have a neighbor in D. Write γ_t for its minimum size. A support is a neighbor of a graph leaf.

## #381: isolates in the support neighborhood (proved)

**Claim.** If T is a tree on n>2 vertices with supports S and Δ_S = max_{s∈S} deg_T(s), then γ_t(T) ≥ isolates(T[N(S)])/(Δ_S−1). The meaning of Δ(S) is the degree in T, not in T[S] (catalogue definition 70).

**Proof.** Write U for the isolated vertices of T[N(S)] and I for those of T[S]. Every u∈U has a neighbor s∈S. This s cannot lie in N(S) since that would give u a neighbor inside T[N(S)]. Hence s∈I and U⊆N(I). Each s∈I belongs to a minimum total dominating set D, since all supports do, and each has at least one neighbor in D. Thus |U∖D|≤Σ_{s∈I}|N({s})∖D|≤(Δ_S−1)|I|. Also U∩I=∅, so |U∩D|≤|D|−|I|. Adding, and using Δ_S≥2, proves the claim.

## Verification scope

This is a written proof, not a full Lean formalization.

AI-assisted work shared for review. No priority claim is made.
