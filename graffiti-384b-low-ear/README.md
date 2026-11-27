# Graffiti.pc #384b with 31 nonleaves and 31 distinct triangle counts

For a finite simple graph G write T for the set of distinct numbers of triangles incident with a vertex. The catalogue bound at |T| = 31 is γ₂(G) ≤ |V(G)| − 16. Each vertex outside a 2-dominating set must have two distinct neighbors in the set. [Ermelinda DeLaVina's Graffiti.pc catalogue](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/index.html)

**Theorem.** If G has exactly 31 vertices of degree at least two, has |T| = 31, and a degree-two vertex has a neighbor of degree at most two, then G satisfies the catalogue bound. The theorem holds at every order, including on disconnected graphs. Any failure at these quotas has precisely 29 vertices of degree at least three and two nonadjacent degree-two vertices whose four neighbor incidences all land among the 29. [Original-graph proof](TwoEarFront.lean)

## Proof

Failure forces the 29 high vertices to have distinct triangle counts, all at least two. Suppose e has a low neighbor. Retain its other neighbor if high, or choose any high vertex c if both neighbors are low. Sample 11 vertices from the 28 high vertices other than c. Both neighbors of e are outside this pool, so e can always be omitted.

At a cubic vertex of triangle count two, the three neighbors induce a path. If the vertex is sampled and both endpoints of that path are retained, the vertex can also be omitted. The only other neighbor that may lose support is the middle vertex of the path, which sees both retained endpoints. High vertices with clique neighborhoods are never adjacent to the cubic score-two vertex, so the saving coexists with the earlier clique-neighborhood removals. There is at most one high vertex of score two. Only three specified draws are required even if the vertex and both endpoints lie in the pool. This gives at least C(25,8) = 1,081,575 samples. [Protecting pair](CubicPair.lean) · [Simultaneous omission](CubicSaving.lean) · [Summed estimate](RootMass.lean)

Rank all 29 high vertices by triangle count, including the retained vertex c. Let m be the number of its neighbors in the pool. At most two triangles through c can involve a low vertex, so its score is at most 2+C(m,2). Its neighbors in the pool already have one retained neighbor. The upper-rank constraint also limits small degrees near the top of the score ordering. Combining the rank that c occupies, these retained-neighbor credits and the cubic saving rules out failure with an integer margin of at least 36,537 over the C(28,11) samples. [Rank certificate](RootRank.lean)

**Further structural restriction.** If the ears have distinct neighbor pairs {a,b} and {a,c} with three distinct high vertices, any common neighbor of b and c in a failure must equal a. Otherwise that neighbor and the two ears form one side of a six-vertex configuration; the three high vertices form the other side. Every vertex has at least two neighbors on the opposite side, and the repository's protected-cut theorem then excludes failure. Four distinct ear neighbors and overlapping pairs satisfying this restriction remain possible in this proof. [Outer-anchor restriction](OuterSeparation.lean)

## Replay

With Lean 4.19.0 and pinned Mathlib v4.19.0, put the compiled prerequisites [CubicExtra](../graffiti-384b-independent-small/) and [EarTriangle](../graffiti-384b-order33-full/) and their prerequisites on the search path. Compile the new modules in the order in `modules.txt` with `lean -DwarningAsError=true`, adding each resulting object to the search path. The original strict audit is below.

[Strict Lean replay](StrictTwoEars.log) · [Exact source hashes](NEW-SOURCES.sha256). The full conjecture remains open.
