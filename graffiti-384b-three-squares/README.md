# Graffiti.pc #384b for three degree-two vertices on four-cycles

In a finite simple graph G, let T be the set of distinct numbers of triangles containing individual vertices, counting zero when realized. A 2-dominating set gives each omitted vertex at least two neighbors in the set. The catalogue bound is γ₂(G) ≤ |V(G)| − ⌈|T|/2⌉. At |T| = 31 this is γ₂(G) ≤ |V(G)| − 16. Call a vertex a nonleaf here if its degree is at least two.

**General theorem.** If three distinct degree-two vertices each lie on a four-cycle, then G satisfies Graffiti.pc #384b. The cycles may coincide or intersect arbitrarily. The result holds at every order and diversity and also for disconnected finite simple graphs. [Original-graph theorem](SquareTriple29.lean)

**Diversity-31 reduction.** Suppose |T| = 31, G has 32 nonleaves, and G violates the catalogue bound. At least one of the three degree-two vertices e has neighbors a,b satisfying N(a) ∩ N(b) = {e}. Equivalently, e belongs to no cycle of length four. The theorem allows a,b to be adjacent or nonadjacent. It imposes no connectedness assumption. [Exact statement](SquareTriple29.lean)

The previous result gives exactly 29 vertices of degree at least three at this quota. The following additional restrictions hold in every counterexample at every diversity.

- If two distinct degree-two vertices e,f both lie on four-cycles, their neighbor pairs have the form {r,a} and {r,b}, where r,a,b are distinct. Either every four-cycle through e has b opposite e, or every four-cycle through f has a opposite f. At most two degree-two vertices can lie on four-cycles.
- If the two neighbor pairs of two distinct degree-two vertices are each contained in a four-clique, the catalogue bound holds. The two cliques may overlap arbitrarily and may coincide.
- Suppose a five-clique contains both neighbors of e. In every protected frame containing a different degree-two vertex f with at most three pins of either color, one neighbor of e must occur on each side. A protected frame consists of disjoint sets A,B in which every vertex has at least two neighbors on the other side. Alternating sides of a four-cycle or six-cycle give examples. The five-clique premise concerns the specific neighbors of e. The mere existence of a five-clique elsewhere gives no such condition.

## Proof

If a protected frame contains two degree-two vertices e,f, pin the frame in a maximum cut and consider the set S consisting of e,f and all h vertices of degree at least three. Every free vertex of this set sees at least two vertices of the opposite color. Each pin already sees two. Either color restricted to S can be omitted. The h high-degree vertices realize at most h distinct counts, and lower degrees contribute only zero and one. Therefore |S| = h + 2 ≥ |T|, and the larger color omits at least ⌈|T|/2⌉. Consequently a counterexample has at most one degree-two vertex in any protected frame. [Cut and frame theorem](SquareFrame29.lean)

Write N(e) = {a,b}. Any other common neighbor x of a,b gives the frame {e,x} opposite {a,b}. Compare two such frames at e and f and try both possible orientations. If both orientations fail, the two neighbor pairs must intersect, and for every pair of choices of fourth vertices x,y, either x belongs to N(f) or y belongs to N(e). Equal neighbor pairs are impossible. For distinct pairs {r,a}, {r,b}, this forces x = b or y = a. Since the choices are independent, one of the two fourth vertices is unique.

Suppose three degree-two vertices each have a four-cycle. Their three distinct, pairwise intersecting neighbor pairs either are the three edges of a triangle or have a common endpoint. In the triangle case, put the three degree-two vertices on one side and their three anchors on the other. This is a protected frame. In the common-endpoint case write the pairs as {r,a}, {r,b}, {r,c}. The forced contacts give all three edges ab, bc, ca, and r is adjacent to at least one of a,b,c. If r is adjacent to a, then a serves as a common choice of fourth vertex for the ears on {r,b} and {r,c}, contradicting the contact restriction. The other choices of neighbor of r work the same way. This proves the reduction without a graph census. [Pair classification, three-vertex proof and original-graph conclusion](SquareTriple29.lean)

For the five-clique restriction, suppose one side of a frame for f misses both neighbors of e. Every possible fourth vertex opposite e must lie on the other side, since otherwise the two frames can be combined. The five-clique supplies three such vertices, all distinct from the neighbors of e. These exhaust a side of size at most three. Now that side also misses both neighbors, so reversing the two sides forces the same three vertices into both sides of a disjoint frame.

## A sharp example for protected frames

Take a triangle on vertices 0, 1, 2, and add vertex 3 on edge 01 and vertex 4 on edge 02, retaining all triangle edges. Both degree-two vertices have a four-cycle. No protected frame contains both. If it did, the shared anchor 0 would force 3 and 4 to the same side, with 0, 1 and 2 on the other. Vertex 1 would then have only one opposite neighbor. The graph has triangle counts 3, 2, 2, 1, 1 and γ₂ = 3, exactly the catalogue bound. Lean verifies the example by finite reduction. It establishes sharpness for the protected-frame claim. [Example.sharp_two](SquareTriple29.lean)

## Replay and source map

| Module | Predecessor and direct uses |
| --- | --- |
| SquareFrame29 | Imports CoverDense31. Uses EarFrame33.Frame, PinnedColor34.cut, Repair.omit_set and the square construction from CubicDiamondCut33. |
| SquareTriple29 | Imports SquareFrame29 and EarFixture33. The latter supplies the minimum test for the five-vertex sharp example. Uses the original-graph 32-nonleaf reduction Cover31.residual, the two-neighbor certificate PinnedColor34.two, and the new contact restriction. |

Extract the archive and enter `graff384b-squares29`. Use Lean 4.19.0 (commit `6caaee842e94`) and built Mathlib v4.19.0 (commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`).

```bash
CROSSFOUR_LEAN_BIN=/absolute/path/to/lean-4.19.0-linux/bin \
CROSSFOUR_MATHLIB=/absolute/path/to/mathlib4-4.19.0 \
bash replay.sh --cold
```

The recorded entry point was `bash replay.sh --checked-base /absolute/path/to/Strict166.log`. It audits 166 frozen modules and 397 axiom reports and rebuilds 80 modules in fresh output directories. The chain covers 246 graph modules and 573 axiom reports. The two new modules contribute ten reports. The build treats warnings as errors and audits the reports against `propext`, `Classical.choice` and `Quot.sound`. The nested predecessor archive has SHA-256 `e88c6b92a6c544805e27040b1b668f345d5122c42c8184dad2c4cf027fac3ec8`.

The diversity-31 case with 29 high-degree vertices remains open. At the 32-nonleaf quota the new result leaves configurations in which at least one of the three degree-two vertices is on no four-cycle. At the 30- and 31-nonleaf quotas the conclusions concerning pairs and individual frames still apply whenever their premises hold.

[Strict transcript](Strict246.log) · [Two new hashes](NEW-SOURCES.sha256) · [All 246 source hashes](SOURCES.sha256) · [Delivery hashes](DELIVERY.sha256)
