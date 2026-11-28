# Graffiti.pc #384b after excluding nonleaf zeros

For a finite simple graph G on n vertices let T be its set of triangle-incidence counts, including zero when realized. The catalogue asks whether γ₂(G) ≤ n − ⌈|T|/2⌉ for connected G of order greater than two. The predecessor proves the inequality whenever some vertex of triangle count zero has degree at least two. Together with the positive-palette theorem this leaves only odd diversity with all zeros on leaves in connected graphs. This supplement gives an all-order pair alternative, an exact nine-vertex equality example, and structural restrictions on one of the remaining triangle-edge profiles. The general leaf case is open here.

## Cut restrictions

Let J consist of the triangle-supported edges of G on the original vertex set, and H its vertices of degree at least three. Suppose G violates the catalogue bound and |H|+1=|T|. Every maximum cut of J splits H equally. Each high vertex has strictly more neighbors across the cut than on its own side. In J, a high vertex with exactly two crossing neighbors is cubic, and has original triangle count two or three. Those scores cannot repeat in a failure, so there are at most two such vertices.

Take a high vertex x on shore A and tentatively omit the high vertices on the opposite shore along with x. If x already has two original neighbors outside the opposite high shore, this fails only if there is a crossing skeleton edge from x to one of the two critical cubic vertices. Each of those vertices has only two crossing neighbors. Consequently at most four high vertices across both shores combined have two original neighbors outside their opposite high shore. The test counts all neighbors of x in the original graph, including attached leaves and unsupported edges. [LeafCritical.lean](LeafCritical.lean) · [LeafExposure.lean](LeafExposure.lean)

## Exact pair alternative

For any finite graph violating the bound, let a,b be distinct nonadjacent vertices. Either some minimum 2-dominating set contains both a and b, or there is a set S of size γ₂(G)−1, disjoint from both, that two-dominates every outside vertex other than a,b. Both endpoints see at least one member of S, and at least one endpoint sees exactly one. This theorem has no skeletal high-count hypothesis. [PairAlternative.lean](PairAlternative.lean)

Add a new vertex z adjacent only to a,b. No new triangle is created, zero is already realized, and the predecessor gives γ₂(G+z)≤γ₂(G). If a minimum extension set omits z, it contains a,b and projects to the first conclusion. Otherwise deleting z can make endpoints deficient. Adding both a,b to this projection restores domination. If that repaired set has minimum size we again have the first conclusion. The strict alternative forces the projection to omit both endpoints and have size exactly one below the original minimum.

## Nine-vertex equality example

The original graph is connected with counts [5,2,3,1,0,4,6,8,10], and its only zero occurs on a leaf. Its three minimum sets are {1,4,7,8}, {4,5,7,8}, and {4,6,7,8}. Vertices 0,1 are nonadjacent. Adding vertex 9 adjacent only to them preserves the palette and has unique minimum set {4,7,8,9}. Removing vertex 9 leaves vertex 1 with exactly one retained neighbor. Both domination numbers equal four, and the original catalogue bound also equals four. The example rules out unconditional projection of extension minima and realizes the second configuration. Whether every genuine failure satisfies the stronger joint-minimum assertion remains undecided. All graph data and the complete minimum-set lists are kernel-checked. [PairExample.lean](PairExample.lean)

## Source provenance and replay

The five source modules consist of four new modules and the exact prior IsolateBasic384b.lean from graff384b-diversity29. Its isolated extension, spectrum lemma and minimum-set existence lemma are reused. The predecessor source archive is pinned to SHA-256 3530c6cdc9ff175a10c1c9d12b24b533bd24ff11db14d53cf578be4c22b0c35a. It embeds the public odd-zero structural baseline archive at commit ac8fb2293cafb5ad4fef1a67c36b12b34c9a36bc. [Published predecessor source](https://github.com/vjdad4m/maths/blob/ac8fb2293cafb5ad4fef1a67c36b12b34c9a36bc/graffiti-384b-odd-zero-structure/proof-sources.zip)

From the extracted source archive use the same Lean 4.19.0 binary and built Mathlib v4.19.0 checkout as the predecessor.

~~~sh
export CROSSFOUR_LEAN_BIN=/absolute/path/to/lean-4.19.0-linux/bin
export CROSSFOUR_MATHLIB=/absolute/path/to/built/mathlib4
python3 -B replay_leaf.py
~~~

This cold entry rebuilds 53 project modules. The alternative command `python3 -B replay_leaf.py --predecessor-log /absolute/path/to/CompleteCold.log` authenticates all 48 prior object hashes in that workspace and recompiles the five leaf-stage modules. The replay checks sources, all five fresh object hashes, warnings as errors, the axiom whitelist, and every printed target. The external discovery search for the nine-vertex example supplies no mathematical coverage claim. [Sources](SOURCES.sha256) · [Objects](OBJECTS.sha256) · [Entry point](replay_leaf.py)

[Complete pinned Lean sources](proof-sources.zip). Extract the archive and use its replay script.
