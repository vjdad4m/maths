# Lean proof of the general cut-vertex case of Graffiti.pc #189

Let n ≥ 2 be a degree threshold. In a finite connected simple graph, suppose
every pair of distinct vertices includes one of degree at least n, and each
even-distance set, including its center, contains at most n+1 vertices.
If deleting a vertex disconnects the graph, then the graph has a spanning
path. The parameter n is not the order of G.

This is a Lean formalization of a known subdomain of the conjecture, not a
new resolution of the paper result. See Rohun Easwar and Shaurya Johari,
[Conditions for traceability under a bound on the size of even-distance sets,
Theorem B(4)](https://arxiv.org/html/2609.11719v1). The Lean proof generalizes
the earlier degree-four repository implementation. It rules out at least
three components at a cut vertex by even-distance counts, bounds the two
remaining components, and uses rooted closure and path splicing for the
extremal sizes.

[Exact original-graph theorem](ArticulationGeneralClosure189.lean) ·
[Strict replay](StrictReplay.log).

Build the pinned [degree-four baseline](../graffiti-189-complete-degree-four/)
with Lean and Mathlib v4.19.0. Keep its compiled objects on LEAN_PATH and
run the archived replay script on the five new modules. All reported Lean
axioms are standard. The unrestricted #189 conjecture remains open.

[Complete pinned Lean sources](proof-sources.zip). Extract the archive and use its replay script.
