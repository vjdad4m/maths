# A cubic ear endpoint is impossible in the extremal core for Graffiti.pc #384b

In the order-33, diversity-33 case the conjectured bound is 16. Here diversity counts the distinct numbers of triangles incident to a vertex, including zero when realized. A 2-dominating set supplies two neighbors to each vertex outside the set. Earlier reductions leave a hypothetical leaf-and-ear counterexample with a 32-vertex positive core H obtained by deleting the leaf. Its vertex triangle counts are pairwise distinct, it has a five-clique, and γ₂(H) = 16. A triangular ear e has exactly two neighbors a,c and they are adjacent.

**Both a and c must have degree at least four in H.** In particular the cubic ear attachment that previously led to a 29-vertex test cannot occur in an extremal core. The result covers every position of the leaf. More generally, in a finite positive core with distinct counts and a five-clique, a triangular ear with a cubic endpoint implies 2γ₂(H) < |V(H)|. No order, connectivity or attachment hypothesis is needed for this strict inequality. [General saving, degree bound, and order-33 lifting theorem](CubicCoreStrict33.lean)

**There is also a restriction at higher degree.** Suppose w is a common neighbor of a,c other than e. If 2γ₂(H) ≥ |V(H)|, each of a,c,w belongs to at least four triangles and has degree at least four. In particular, if either endpoint has triangle count two or three, e is the only common neighbor of a,c. [Three-vertex restriction](CubicSquareProfile33.lean)

The order-33 lifting theorem gives γ₂(H) ≤ 15 and γ₂(G) ≤ 16 whenever an ear endpoint is cubic, or has count two or three and the edge ac belongs to another triangle. A 15-vertex solution in H extends by putting the deleted vertex into the set. The full graph can have any attachment at that vertex. The proof does not establish equality of the full domination number with 16. Cases with both endpoints of degree at least four surviving the count restriction remain open, as do lower-diversity cases. These results give no counterexample.

## Proof of the strict inequality

Write s(y) for the number of triangles at y. The ear has count one. First suppose there is a second common neighbor w and s(a) is two or three. Assume 2γ₂(H) ≥ |V(H)| and fix a five-clique C.

1. The alternating four-cycle e,a,w,c forms two sets of pins in which every vertex already sees two opposite pins. The checked clique-overlap theorem forces C to meet this cycle at least twice. Otherwise cubic vertices outside the cycle realize both counts two and three, contradicting injectivity at a. Neither e nor a can be in C, since a vertex in C participates in at least six triangles. Thus c and w belong to C. [Cliques and pins](CubicDiamondCut33.lean)
2. For each x among the other three vertices of C, omit x from both candidate sets. Pin the four retained clique vertices two per side, with c and w opposite, and join these pins to the alternating four-cycle. If both candidate sets cannot be completed, a vertex outside the pins must be cubic and adjacent to x. Its triangle count is the remaining one of two and three. Injectivity makes this the same vertex u for every x. Consequently N(u) is exactly the three vertices C minus c,w. Every cubic lies in {a,u}, and every five-clique is determined by c,w,u. [Exact neighborhood](CubicClosure33.lean)
3. Name the three neighbors of u as x,y,z. Omit x again, this time using a different coloring. The first set of pins is {a,c,y,z} and the second is {e,w,u}. The omitted x sees y,z on the first side and w,u on the second. The pins a,c both see e,w. Each of y,z sees w,u. The pins e,w both see a,c, and u sees y,z. Every remaining unpinned vertex has degree at least four and therefore retains at least three neighbors when x is omitted. A maximum cut with these pins extends both candidate sets. Their total size is one less than the order, contradicting the assumed lower bound on γ₂(H). [Second coloring](CubicCoreStrict33.lean)
4. If a is cubic, the preceding checked ear-neighborhood lemma shows s(a) = 2 and gives the required w. This proves the degree result. If w itself has count two or three, the overlap argument puts a,c in the five-clique. The checked clique-edge theorem requires the cubic of that count to see at most one of a,c, whereas w sees both. This proves the last count restriction. [Third vertex](CubicSquareProfile33.lean)

The earlier 29-vertex graph was obtained by deleting e,a,c from H. The contradiction now occurs in H itself. An ordinary 29-vertex graph can still have 2-domination number 15 and one degree-two ear.

## Independent residual path lemma

The three Residual modules prove an additional statement directly on a 29-vertex graph J. Suppose γ₂(J) = 15, v is a degree-two ear with adjacent neighbors p,q and all other degrees are at least three. Remove v,p,q. Every remaining neighbor of p is connected in the induced graph to every remaining neighbor of q. Components without a contact are allowed. This lemma is independent of the proof of the strict inequality above. [Connected contacts](ResidualContacts33.lean)

To see the reason, two different components with a contact at each end would provide two disjoint sets of pins, each needing one further opposite neighbor at its root. Within each component use a longest simple path from its root. If the terminal vertex has three neighbors on the path, two have the same index parity. If its third neighbor is the other root, the known odd parity of all routes between the roots enforces the same parity for the two path neighbors. In either case the prefix and the two terminal edges supply alternating pins. Putting v opposite both roots supplies each root's missing neighbor. A pinned maximum cut would then give a 14-vertex solution. [Alternating pins](ResidualArms33.lean) · [Longest-path argument](ResidualLongest33.lean)

## Dependency and replay map

| Module | Direct import | Role |
| --- | --- | --- |
| CubicDiamondCut33 | AnchorEdge33, frozen | Clique overlap and the blocker at one omitted vertex |
| CubicClosure33 | CubicDiamondCut33 | The three vertices forced to be the neighborhood of one cubic |
| CubicCoreStrict33 | CubicClosure33 | Strict saving, degree and endpoint count bounds, lifting to order 33 |
| CubicSquareProfile33 | CubicCoreStrict33 | All three non-ear vertices of two triangles sharing the ear edge |
| ResidualArms33 | AnchorEdge33, frozen | Compatible pin sets and their completion |
| ResidualLongest33 | ResidualArms33 | Construction from a longest path in one component |
| ResidualContacts33 | ResidualLongest33 | Connectivity of all contacts with the two endpoints |

The proof uses EarAttachment33.frame_obstruction, EarOnClique33.mixed_blocker and edge_restriction, EarAnchor.diamond and gamma_induced_iff, plus the pinned maximum-cut results. The supplementary argument uses the existing OneEar.Route and AnchorParity.odd_routes. The public #299 transversal estimate and #397c square-domination lift do not give the two simultaneous color classes used here. [Repository index](https://github.com/vjdad4m/maths/blob/main/README.md) · [Clique overlap](https://github.com/vjdad4m/maths/blob/main/graffiti-384b-ear-exchange/EarAttachment33.lean) · [Pinning and clique-edge restrictions](https://github.com/vjdad4m/maths/blob/main/graffiti-384b-ear-exchange/EarOnClique33.lean)

Use Lean 4.19.0 and the prepared Mathlib checkout at
`c44e0c8ee63ca166450922a373c7409c5d26b00b`. From the repository root:

```bash
CROSSFOUR_LEAN_BIN=/absolute/path/to/lean-4.19.0-linux/bin \
CROSSFOUR_MATHLIB=/absolute/path/to/mathlib4-4.19.0 \
bash graffiti-384b-cubic-ear-closure/replay.sh
```

The replay uses the published [cubic anchor package](../graffiti-384b-cubic-ear-anchor/)
and exact new source hashes. All scope theorems were checked with warnings
as errors and only standard Lean axioms.
