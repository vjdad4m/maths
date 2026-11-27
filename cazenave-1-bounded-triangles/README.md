# Cazenave Conjecture 1: bounded local triangle counts

**Partial result.** Let G be a connected finite simple graph, m its edge
count, and let k bound the number of triangles through every vertex.
For the lower eigenvalue t in an ordered pair of nonzero orthogonal
adjacency eigenvectors, the theorem proves R(G) ≥ t+1 whenever

    m ≥ (2 + sqrt(1 + 3k))² + k.

There is no condition on the triangles in the sign supports. In particular,
k=1 is sufficient with m≥17. An alternative sufficient condition on the
same original graph is t>0 and 3k≤t(t−2).

## Proof

The sum of degrees over any set S is at most m plus the number of edges
with both endpoints in S. In a neighborhood the latter number is exactly
the number of triangles through the central vertex. Cauchy–Schwarz on
edge weights gives R≥m/sqrt(m+k) and hence R≥sqrt(m−k) whenever m≥k.
The same local triangle bound is inherited by induced subgraphs. For positive
t, the adjacency inequality on each sign support implies
t²≤m_support+k by applying it twice at a maximum of the truncated
eigenvector. Thus m≥2t²+1−2k, since connectivity leaves a crossing edge
outside the two supports. When 3k≤t(t−2), this gives m−k≥(t+1)².
When t is below the threshold 1+sqrt(1+3k), the assumed lower bound on m
directly gives m−k≥(2+sqrt(1+3k))². Neither proof assumes triangles are
absent in the sign supports.

The named Lean results are `CazenaveOne.bounded_triangles` and
`CazenaveOne.bounded_triangles_many_edges` in Neighbor.lean. The more
targeted `CazenaveOne.nodal_neighbor_excess` in Excess.lean allows the
three actual neighborhood degree excess bounds (whole graph, positive
support, negative support) instead of charging k three times.

The Randić index in the theorem uses the exact sum over unordered edges.
The standard real symmetric spectral theorem supplies the ordered
orthogonal eigenvectors for t=λ₂ in ordinary mathematics; that bridge
is not part of the Lean proof. This does not establish Cazenave's full
Conjecture 1 ([preprint, §7](https://arxiv.org/abs/2611.03879v1)).

## Replay

Use Lean 4.19.0 and Mathlib commit c44e0c8ee63ca166450922a373c7409c5d26b00b.
Run `lake env bash /absolute/path/to/this/package/replay.sh` from the pinned Mathlib checkout.
The unchanged support modules come from the adjacent [triangle-free package](../cazenave-1-triangle-free/). All theorem axiom prints
report only propext, Classical.choice, and Quot.sound.
