# Graffiti.pc #232

[Graffiti.pc catalogue](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/), with the [exact statements](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json) and [definitions](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/definitions.json).

## #232: Radius and eccentricity of the periphery

Let t=γ_t(G), r=rad(G), B the vertices of maximum eccentricity, and e=max_z dist(z,B), with zero if B=V. The claim is 2t ≥ r+e.

A minimum total dominating set D induces at most floor(t/2) components of order at least two. Assign each outside vertex to a component it touches. The graph of interclass connections is connected. For each edge in a spanning tree of these classes, add at most two outside vertices (endpoints of a crossing edge) to connect its two D-components. Thus there is a connected dominating set C of order k≤2t−2. This is also the classical Favaron–Kratsch bound.

Take a spanning tree T on C and a tree diameter path P of q edges; put O=k−1−q, the number of edges off P. A midpoint of P has eccentricity at most ceil(q/2) in T; any G-vertex outside C has a C-neighbor. Thus r≤ceil(q/2)+1, which suffices if e=0.

If e>0, choose diameter endpoints a,b and a vertex z at distance e from B. All three graph pairwise distances are at least e. Pick representatives a',b',z' of C within one graph edge of the three vertices. Project these representatives onto P (nearest tree points). Two of the three coordinates on the q-edge path have gap at most floor(q/2). The tree path between their representatives then uses at most floor(q/2) path edges and at most O other edges. Consequently e≤2+floor(q/2)+O. Summing gives r+e≤q+O+3=k+2≤2t.

## Verification scope

The graph argument is a written proof, not a full Lean formalization.

AI-assisted work shared for review. No priority claim is made.
