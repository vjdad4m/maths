# A proof of Graffiti.pc Conjecture 161

[Ermelinda DeLaViña's November 2026 catalogue](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/wowiiaii.pdf) lists Conjecture 161 as open. [Douglas B. West's problem list](https://dwest.web.illinois.edu/regs/graffiti.html) records the same statement. This entry records an elementary Lean formalization, not a claim that the proof or result is new.

**Conjecture.** For every finite simple connected graph G, the maximum number L_s(G) of leaves of a spanning tree is at least the maximum local independence number of the complement of G. The local independence number at a vertex is the largest size of an independent subset of its open neighborhood.

**Proof.** Let I be an independent set in the complement's open neighborhood of any vertex v. In G, I is a clique. It is proper because v is not in its own open neighborhood. If I is empty, the bound is automatic. Otherwise, connectivity supplies an edge xy with x in I and y outside I. The star in G centered at x, with leaves (I minus {x}) union {y}, has exactly |I| listed leaves, including when |I|=1. Extend it to a spanning tree by repeatedly adding one new vertex by an edge to the existing tree. Each addition creates a new leaf and removes at most one old leaf, so the number of leaves never decreases. This proves L_s(G) ≥ |I| for every such I, hence proves the conjecture.

In fact the proof gives L_s(G) ≥ |C| for **every proper clique** C in any finite connected graph. This is a consequence of the standard star-extension argument, not a claim of a new general graph-theoretic technique.

## Lean replay

Run `lean -DwarningAsError=true Proof161.lean` with Lean 4.19.0. The proof uses Lean core, not Mathlib. The graph is represented by a binary adjacency relation; a tree starts with one vertex and grows by adding edges to fresh pendant vertices. This construction ensures each resulting graph is a tree. Connectivity is given by finite walks, and a leaf has exactly one neighbor. The proof explicitly constructs a spanning tree and a list of distinct degree-one vertices. There are no placeholders or custom axioms.
