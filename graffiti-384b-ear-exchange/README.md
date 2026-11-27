# Leaf exchange and ear geometry for Graffiti.pc #384b at order 33

The conjecture concerns a connected finite simple graph of order greater than two. Write $T$ for the distinct counts of triangles through individual vertices, including zero when it occurs. It asks whether `gamma G ≤ bound G`, where `gamma` is the minimum size of a set providing two neighbors to each vertex outside it, and `bound G = n - (|T|+1)/2` uses natural-number division. With 33 vertices and 33 counts the target is 16.

The previous verified reduction gives a possible failing graph with a unique leaf $z$, a unique degree-two triangular ear $e$, distinct counts and a five-clique. Deleting $z$ gives a connected 32-vertex positive induced core $H$ with 2-domination number 16. Write $a$ for the leaf's neighbor and $b,c$ for the ear's two adjacent neighbors. In the results below, degrees, triangles and neighborhoods are taken **in the positive core**. A cubic root has degree four in the full graph. The leaf-and-ear case remains open.

## Exact attachment test

The full graph has a 2-dominating set of size at most 16 **if and only if** the positive core has a minimum 2-dominating set $D$ with all three properties below.

1. The root $a$ belongs to $D$.
2. The root has exactly one neighbor in $D$.
3. Every vertex outside $D$ adjacent to $a$ has at least three neighbors in $D$.

Under these conditions, exchange $a$ for the leaf. In the converse direction, remove the leaf from a 16-vertex solution. The 15 remaining vertices cover every ordinary core requirement except the root, which has exactly one retained neighbor. Inserting the root gives the required minimum set. [Abstract half-order equivalence](Exchange33.lean) · [Equivalence for the full leaf attachment](EarRoot33.lean)

## Restrictions on a failure

A *frame* here means disjoint pin sets in which every vertex already sees two vertices in the opposite set. Alternating colors on any simple even cycle give a frame. More generally the formal construction `alternating_frame` allows a disjoint union of cycles. The root set in the general cut lemmas consists of vertices credited with one permanent neighbor outside the positive core. For a leaf it is the singleton consisting of $a$.

- Every frame containing the ear meets every five-clique. If the intersection has one vertex, there are exactly two cubic vertices in the core, of triangle counts 2 and 3. Both lie outside the frame and the clique, and neither is the root. Each sees two of the remaining four clique vertices. These two pairs partition those four vertices. In particular, if the root is cubic, every even cycle through the ear meets every five-clique at least twice. [Frame theorem](EarAttachment33.lean)
- If both ear neighbors belong to a five-clique, the core again has exactly two cubics, of counts 2 and 3. They both lie outside the clique and miss the root set. They cover the other three clique vertices. Each sees at most two of those three and at most one of the two ear neighbors. [Simultaneous pinning on the clique edge](EarOnClique33.lean)
- If the edge $bc$ belongs to at least four triangles, the core must have a cubic of count 2 and a cubic of count 3, both different from $a$. If either required cubic is unavailable, the edge has at most three incident triangles in total, including the ear triangle. In this case no five-clique contains both $b,c$. Every common neighbor of $b,c$ other than the ear belongs to every five-clique. When such a common neighbor exists, each five-clique contains exactly one of $b,c$. This applies in particular to every cubic root. The need for both cubic scores at a thick ear edge already follows from the half-order lower bound on the positive core before any leaf is attached. [General scarcity and thickness theorems, and the order-33 specialization](EarOnClique33.lean)
- Even at an unrestricted root, for any five-clique missing both $b,c$, every common neighbor of $b,c$ apart from the ear must belong to that clique. [Common-neighbor theorem](EarAttachment33.lean)

The proof combines a frame around the ear with a two–two split of four vertices of a five-clique, omitting the fifth clique vertex from both candidate sets. Two frames that share one pin can be oriented consistently. After maximizing the cut with these pins, a deficient cubic cannot spoil both candidates if it already sees two pins of one color. Deficient vertices of different colors can be protected simultaneously. Counting the remaining blockers uses injectivity of triangle counts and the fact that the ear already realizes count 1. For the bound of three triangles on $bc$, three further common neighbors would all lie in a fixed five-clique. They would therefore form a triangle and, with $b,c$, a forbidden five-clique on the ear edge. [Frame merge](EarFrame33.lean) · [Mixed protection](EarOnClique33.lean)

## Checked small example

A six-vertex positive core with a unique triangular ear and domination number three gives different outcomes at two cubic roots. Its triangle counts in vertex order are `[5,3,2,2,2,1]`. Vertices 2 and 3 both have degree three, both have triangle count two, and both miss the ear at vertex 5. A leaf at vertex 2 leaves the domination number at three. A leaf at vertex 3 raises it to four. For the former, `{0,1,6}` is a 2-dominating set. The Lean proof checks the two exact minima over all vertex subsets by kernel reduction. This example has repeated counts and lacks a five-clique, so it addresses the attachment test only. A Python search suggested the six-vertex graph. The published #398-style finite minimum argument was reused through the preceding #384b finite certificates. [Kernel-checked example and adjacency lists](EarFixture33.lean)

## Files and replay

The six modules reuse the published [leaf-and-ear frontier](../graffiti-384b-leaf-ear/).
Use Lean 4.19.0 and the prepared Mathlib 4.19.0 checkout at
`c44e0c8ee63ca166450922a373c7409c5d26b00b`. From the repository root:

```bash
CROSSFOUR_LEAN_BIN=/absolute/path/to/lean-4.19.0-linux/bin \
CROSSFOUR_MATHLIB=/absolute/path/to/mathlib4-4.19.0 \
bash graffiti-384b-ear-exchange/replay.sh
```

| Module | Direct import | Main contribution |
| --- | --- | --- |
| `Exchange33` | `FrontierEar33` | Minimum-set exchange at a single credited root |
| `EarFrame33` | `Exchange33` | A clique cut merged with an ear frame sharing at most one vertex |
| `EarAttachment33` | `EarFrame33` | Exact overlap, cubic coverage, even cycles and common neighbors |
| `EarRoot33` | `EarAttachment33` | Both directions of the full-graph attachment equivalence |
| `EarOnClique33` | `EarRoot33` | Mixed pin protection, cubic availability and the three-triangle bound |
| `EarFixture33` | `Exchange33` | Two inequivalent attachments of the same six-vertex core |

The argument reuses `CliquePivot33.shared`, `isolated_degree`, `full_cubic`, `PositiveCore33.extremal_core`, `rooted_tight`, and `PinnedColor34.two` from the pinned release. The prior clique-pivot coverage theorem assumed minimum degree three at every uncredited vertex. The ear has degree two and needs its own pins here. The previously checked #299 transversal estimate supplies a numerical bound, while the converse of the attachment test requires tracking exactly which vertex loses demand.

The six new modules passed strict replay with only the standard axioms.
