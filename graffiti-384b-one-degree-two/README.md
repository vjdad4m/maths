# Graffiti.pc #384b with one degree-two vertex

**If a finite simple graph has 29 distinct vertex triangle counts, at least 29 nonleaves, and at least 28 vertices of degree at least three, it has a 2-dominating set of size at most its order minus 15.** The new cases have 29 or 30 nonleaves and exactly 28 vertices of degree at least three. The proof works for disconnected graphs. [Numerical theorem](Remaining29.lean)

A nonleaf has degree at least two. A triangle count is the number of unordered triangles through a vertex. Diversity counts the distinct values, including zero when realized. For diversity t and order n, the catalogue bound is γ₂(G) ≤ n − ⌈t/2⌉. Every vertex outside a 2-dominating set must have at least two neighbors inside it. [Ermelinda DeLaVina’s Graffiti.pc catalogue](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/index.html) · [Checked problem index at 00e0e600](https://github.com/vjdad4m/maths/blob/00e0e6005214d3325d521650bf17f11973667419/README.md)

## A single ear at any diversity

Write q for the number of nonleaves and h for the number of vertices of degree at least three. When t ≤ q, **at most one vertex of degree two suffices for the catalogue bound**. If t is even this also holds for q < t, using the earlier even-diversity theorem. The case q = t with one degree-two vertex is the substantive step. [General theorems](PreserveEar.lean)

Call the degree-two vertex e. At q = t, at most two nonleaves can have triangle count zero or one. Indeed, the remaining nonleaves contribute at most one value each, and all other vertices contribute only zero. The ear already uses one of the two places. Consequently there is at most one high vertex f on fewer than two triangles.

Retain all triangle edges and all edges incident to e or f. Every high vertex other than f lies on at least two triangles and therefore keeps at least three neighbors. The two retained stars preserve the degrees of e and f. All vertex triangle counts are unchanged. The resulting spanning graph has the same single ear, and every edge away from e and f belongs to a triangle. A 2-dominating set in this graph works in the original. [Edge trimming and lifting](TriangleStars.lean)

Let a and b be the two neighbors of e. Remove the edges internal to {e,a,b}. If a and b become separated, orient the maximum cuts of their components to put both opposite e. When an anchor needs support, the component cut gives it one opposite neighbor, and e supplies the second. Otherwise take a simple route from a to b. It has length at least two and avoids e. An even route closes through e into an even cycle whose two sides can be extended by the earlier cut theorem. On an odd route, the first and last edges have disjoint endpoints. One of them avoids f, so it belongs to a triangle. The earlier parity-change theorem applies to that end, including when the triangle’s third vertex lies elsewhere on the route. This proves the bound even when e has triangle count zero and its two neighbors are nonadjacent. The argument takes the single exceptional vertex idea from the 31/31 proof and handles it by choosing the route end. [Exceptional-vertex proof](SingleTip.lean) · [Earlier one-ear route and cut package](https://github.com/vjdad4m/maths/tree/00e0e6005214d3325d521650bf17f11973667419/graffiti-384b-one-ear) · [31/31 proof](https://github.com/vjdad4m/maths/tree/00e0e6005214d3325d521650bf17f11973667419/graffiti-384b-uniform31)

## Two ears with 28 high vertices

For q = 30, h = 28 there are two degree-two vertices. The earlier 31-type clique-pivot proof only needs the relation t = h + 1 for its cut and counting steps. In a failure each vertex in a five-clique then has a cubic neighbor. There are at most three cubics. Counting their possible contacts excludes a seven-clique. If a degree-d vertex with d ≤ 8 exceeded its balanced tripartite neighborhood edge bound, it would lie in a five-clique. Removing a cubic neighbor leaves too few missing edges to prevent a seven-clique. Hence the local cap holds, and the previously checked diversity-29 sampling theorem supplies the fifteenth omission. [General pivot cut](QuotaPivot.lean) · [Clique contact counts](QuotaClique.lean) · [Local cap and application](QuotaCap.lean) · [Original 31-type pivot proof](https://github.com/vjdad4m/maths/blob/00e0e6005214d3325d521650bf17f11973667419/graffiti-384b-rich-degree31/CoverDense31.lean) · [Diversity-29 sampling theorem](https://github.com/vjdad4m/maths/blob/00e0e6005214d3325d521650bf17f11973667419/graffiti-384b-diversity29/QuotaLocal29.lean)

## Remaining 29-type cases

The published diversity-29 package already excludes q ≥ 31 and q < 28. At q = 28 the parallel core proof requires a connected triangle-edge graph with a four-clique and one degree-two vertex in that triangle-edge graph. Its shared-cubic and five-clique restrictions are independent of this delivery. [Published 29-type reduction](https://github.com/vjdad4m/maths/tree/00e0e6005214d3325d521650bf17f11973667419/graffiti-384b-diversity29)

| Nonleaves q | What remains |
| --- | --- |
| 28 | The parallel positive-core case. |
| 29 | Exactly 27 high vertices and two degree-two vertices. |
| 30 | Exactly 27 high vertices and three degree-two vertices. The earlier degree-four-to-eight five-clique witness is still required. |

In the last two rows, every high vertex has a distinct triangle count of at least two. Both zero and one occur, and some degree-two vertex has count one. Keep every triangle edge and every edge incident to a degree-two vertex of count zero. This spanning graph has exactly the original triangle counts, high vertices and nonleaves. If the original fails, so does this graph. Every remaining edge outside triangles therefore meets one of at most one designated vertex for q = 29, or at most two for q = 30. These are necessary conditions on a hypothetical failure. [Residual and spanning-graph theorems](Remaining29.lean)

## Strict replay

Use Lean and Mathlib 4.19.0 (Lean commit `6caaee842e94`; Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`). Build the [diversity-29 predecessor](../graffiti-384b-diversity29/) and its documented dependencies. With their objects and the pinned Mathlib environment on the Lean search path, compile the seven modules in `modules.txt` order:

```sh
sha256sum -c NEW-SOURCES.sha256
mkdir -p build
export LEAN_PATH="$PWD/build:${LEAN_PATH:-}"
while read -r module; do
  lean -DwarningAsError=true -DElab.async=false -o "build/$module.olean" "$module.lean"
done < modules.txt
```

The [recorded strict replay](PackedReplay.log) rebuilt all seven modules from the extracted source archive after verifying 164 predecessor hashes; all 20 declarations report only `propext`, `Classical.choice`, and `Quot.sound`. A recursive cold rebuild was not part of the recorded verification.
