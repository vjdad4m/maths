# A zero-count vertex with a low-degree neighbor in Graffiti.pc #384b

**For a connected simple graph on 33 vertices with 33 distinct vertex triangle counts, a zero-count vertex adjacent to a vertex of degree at most four implies γ₂ ≤ 16.** The degree condition refers to the original graph. The zero-count vertex can have any degree. [Full-graph theorem `zero_neighbor_bound`](ZeroNeighbor33.lean)

The catalogue defines γ₂ as the minimum size of a vertex set such that every vertex outside it has at least two neighbors in the set. The diversity is the number of distinct vertex triangle-incidence counts, including zero when realized. For order and diversity both 33 the catalogue bound ⌊33 − 33/2⌋ is 16.

**Exact leaf attachment.** Delete a leaf z with neighbor b. Suppose the 32-vertex induced core H has positive pairwise distinct triangle counts, a five-clique, a triangular degree-two vertex e, and γ₂(H) = 16. If b has degree three in H, reattaching z gives γ₂ = 16. This covers the case in which e is the only common neighbor of its two neighbors and at least one of those neighbors has degree six or greater. There is no restriction on their degrees or their number of common neighbors in the checked theorem. [`attachment_value`](CubicRootFinish33.lean)

A core form holds at any finite order. Under the same triangle, ear and clique hypotheses, if 2γ₂(H) ≥ |V(H)| and b is cubic, there is a set of size strictly less than half the order that supplies two neighbors to each omitted vertex, allowing b one neighbor when omitted. This is the precise meaning of `¬Tight H {b}`. [`cubic_root`](CubicRootFinish33.lean)

## Proof

Let a,c be the neighbors of e in the core. Assume that every set satisfying the relaxed condition at b has size at least half the core order. The ear occupies triangle count one. Each cubic vertex has count two or three, so at most one cubic u other than b exists. The earlier shared-neighbor theorem implies e is the only common neighbor of a,c. In a five-clique C, call x safe if it has no cubic neighbor other than b.

1. Deleting a safe x forces every simple path from a to c that avoids e to have odd length. If exterior triangles at both a and c survive the deletion, the component of the first triangle away from a,c,e,x cannot touch c. Such a contact would give a path meeting the first triangle twice, and replacing the appropriate section gives an even path. The two triangle components therefore lie in disjoint regions, each attached at its own endpoint. Switching the cut on one component puts a and c on the same side while keeping a two-against-two split of the four retained clique vertices. Extending this cut supplies a relaxed set below half. Thus any safe pivot other than a,c must destroy every exterior triangle of at least one endpoint. [Separation](PrivateShores33.lean) · [Cut](PrivatePivot33.lean)
2. There are at least two safe clique vertices, since u can have at most three neighbors. Two safe choices force both a,c outside C. For any exterior edge E in the neighborhood of a and F in that of c, every safe clique vertex belongs to E ∪ F. If the exterior of one endpoint misses C, all exterior edges at the other endpoint contain the safe set. That set must be a pair and the other endpoint has triangle count two. If both exteriors meet C, choose respective contacts p and q. They are distinct. Removing a third safe x would retain the even path a,p,y,q,c for a fourth clique vertex y. Again the safe set is exactly a pair, this time {p,q}. [Edge and contact constraints](PrivatePairs33.lean) · [Two safe choices](PrivatePalette33.lean)
3. Exactly two safe vertices force the second cubic u to exist and all three of its neighbors to lie in C. Thus u has triangle count three and b has count two. Both ear endpoints have degree at least four by an earlier core theorem. Injectivity therefore excludes triangle count two at either endpoint, leaving the two contacts p,q.
4. Omit one neighbor x of u from C. Put its two other neighbors together with a,c on one side of a partial cut. Put p,q,u,e on the other side. The contacts p and q protect a and c alongside e. The other two retained clique neighbors protect u, and x sees two clique vertices on each side. The checked cut obstruction now requires another cubic distinct from u and b. This contradicts the two available cubic scores. The rooted exchange theorem lifts the strict saving to exact equality after the leaf is attached. [Explicit cut](PrivateFrame33.lean) · [Cubic-root theorem and lift](CubicRootFinish33.lean)
5. For the intrinsic full-graph theorem, suppose z has count zero and a neighbor b of degree at most four. In a hypothetical failure, deleting z gives b degree at most three and leaves an extremal positive core. The previously checked dichotomy either provides an ear distinct from b, or gives minimum degree three with every cubic nonadjacent to z in the original graph. The second alternative contradicts the choice of b. In the first alternative, every core vertex other than the ear has degree at least three, so b is cubic. Applying the cubic-root theorem gives the contradiction even if z has more than one neighbor. [Full-graph proof](ZeroNeighbor33.lean)

From the repository root, with Lean and a built Mathlib v4.19.0 checkout:

```bash
CROSSFOUR_LEAN_BIN=/absolute/path/to/lean/bin \
CROSSFOUR_MATHLIB=/absolute/path/to/mathlib4 \
bash graffiti-384b-cubic-root/replay.sh
```

The [strict transcript](Strict202.log) records the original audit and the [source hashes](NEW-SOURCES.sha256) pin the eight new modules.
