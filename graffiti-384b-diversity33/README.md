# Graffiti.pc #384b at triangle-count diversity 33

Let n > 2 be the order of a finite connected simple graph. For each vertex count the triangles containing it. Let T contain the distinct counts, including zero if it occurs. A set is 2-dominating if each vertex outside it has at least two neighbors in it. The minimum size of such a set is γ₂. The catalogue inequality is γ₂ ≤ floor(n − |T|/2). The Lean expression for the right side is `n - (|T| + 1) / 2` with natural-number division.

**Result.** The catalogue inequality holds at every graph order when |T| = 33. In particular, every connected 33-vertex graph with pairwise distinct triangle counts has a 2-dominating set of size at most 16. Combining this with the earlier results for |T| = 32 and |T| ≥ 34 establishes the inequality throughout |T| ≥ 32. Every possible counterexample therefore has an induced connected counterexample on 3 through 33 vertices with the same set of at most 31 triangle counts. The conjecture at smaller diversity remains open in general. [Final theorems](Diversity33Finish.lean)

## The obstruction and the construction

1. A hypothetical failure at diversity 33 has a connected induced failure with the same 33 counts, each at a different vertex, and a vertex of count zero. Deleting this vertex gives a 32-vertex graph H. Its counts are distinct and positive, and γ₂(H) = 16. These are the earlier theorems `OneEar.diversity33_failure` and `PositiveCore33.extremal_core`.
2. In H, the vertices of counts two and three are both cubic, and both miss the deleted vertex in the original graph. To see why the ear case forces both, retain the edges belonging to triangles. This preserves every triangle and five-clique. The earlier degree-four closure then forces at least five retained edges at each endpoint of the ear, so each endpoint has count at least three. With only one available cubic, the existing clique coloring argument forces contacts for both endpoints and a second cubic. The minimum-degree-three case follows from the earlier core dichotomy. [Triangle edges](SupportedEar33.lean) · [Two required cubics](BothCubics33.lean) · [Lift to the original graph](FullScorePair33.lean)
3. Write u and v for the cubics of counts two and three. At least three vertices of every five-clique belong to N(u) ∪ N(v). At most two of its vertices can belong to N(u), since three mutually adjacent neighbors would give u count three. Hence A = N(v) meets every five-clique. The three vertices of A are pairwise adjacent. The exterior W, obtained by deleting v and A, has order 28 and contains no five-clique. [Clique coverage](CubicOverlap33.lean) · [Transversal in the original graph](FullObstruction33.lean)
4. Choose one x in A. Retain the other two vertices of A, select ten vertices of W, and add each unselected vertex of W still having fewer than two selected neighbors. Both x and v already see the two retained vertices of A. The estimate below shows that one choice has at most three additions. This gives a 2-dominating set in H of size at most 2 + 10 + 3 = 15, contradicting 16. The construction allows arbitrary degrees at the neighbors of the original zero vertex. [Construction and proof](ThreeFinish33.lean)

### Counting deficient vertices

There are 3 × C(28,10) = 39,369,330 choices. For w in W, let b count its neighbors in W and j count its neighbors in A. If w has zero retained neighbors in A, at most C(27−b,10) + b C(27−b,9) samples leave it unselected and deficient. If w has one retained neighbor, the bound is C(27−b,10). If it has two, the bound is zero. Let B(b,g) denote these three bounds. Summing over the omitted x gives at most j B(b,j−1) + (3−j) B(b,j) deficiencies for w, with natural-number subtraction. Call this sum F(w). [Fiber counts](ThreeFibers33.lean)

For each w in W its b neighbors in W form a graph with no four-clique. For j ≤ 1 the resulting upper bound on the triangle count of w is the number of edges in the balanced three-partite Turán graph on b vertices plus bj. For every exterior vertex the ordinary bound C(b+j,2) also holds. For an anchor a in A, let b count its neighbors in W. Its triangle count is at most 3 + 2b plus the number of edges in the balanced four-partite Turán graph on b vertices. These constraints use the fact that W has no five-clique. [Graph inequalities](ThreeGeometry33.lean)

Rank the 31 vertices of A ∪ W together, starting at zero. Their distinct positive counts omit three. At rank i the count is therefore at least i+1 for i < 2, and at least i+2 afterwards. The finite arithmetic lemma checks one budget q(i) for each rank. For an exterior vertex it verifies F(w) + 370,000j ≤ q(i). For an anchor it verifies 3,665,432 ≤ q(i) + 370,000b. On summation the incidence terms cancel because each edge between A and W is counted once from each side. The budgets sum to 168,339,458. The total number of deficiencies is therefore at most 157,343,162. Four per choice would require 157,477,320. The margin is 134,158. Lean checks the finite table by kernel reduction and proves that it covers the ranks and degrees of every eligible graph. [Table, rank proof and incidence sum](ThreeBudget33.lean)

From the repository root, with Lean and a built Mathlib v4.19.0 checkout:

```bash
CROSSFOUR_LEAN_BIN=/absolute/path/to/lean/bin \
CROSSFOUR_MATHLIB=/absolute/path/to/mathlib4 \
bash graffiti-384b-diversity33/replay.sh
```

The [strict transcript](Strict217.log) records the original audit and the [source hashes](NEW-SOURCES.sha256) pin the fifteen new modules.
