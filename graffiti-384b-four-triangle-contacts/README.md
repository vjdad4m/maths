# Graffiti.pc #384b at four and five triangle contacts

Let G be a finite simple graph with 29 distinct vertex triangle counts, 29 vertices of degree at least two, and 27 vertices of degree at least three. There are two degree-two vertices, called the ears. In the remaining case their neighborhoods are disjoint and consist of four high-degree vertices. Write W for these four anchors, X for the other 23 high-degree vertices, and T for the number of vertices of X on a triangle with an anchor. All results allow disconnected graphs. The target in this profile is γ₂(G) ≤ |V(G)| − 15. [Ermelinda DeLaViña’s Graffiti.pc catalogue](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/index.html)

**The catalogue inequality holds whenever T ≤ 4.** The previous local proof stopped at three. Consequently a failure needs 5 ≤ T ≤ M ≤ 14, where M counts vertices of X with any neighbor outside X. The frozen double-contact caps still apply. If M = 14, at most six vertices of X have two exterior neighbors. If M = 13, at most ten do. The general four-anchor case remains open. [Profile theorem and residual](TenFront.lean)

## Why four contacts suffice

Take the two ears, their four anchors and four further high vertices containing all T triangle contacts. These ten vertices contain every triangle through each anchor. At maximal diversity the four anchor triangle counts are distinct and at least two. The degrees and score facts are inherited from FourFront’s failure reduction.

The four additional vertices induce one of eleven simple graphs up to isomorphism. Lean certifies a relabeling for every one of the 64 labeled graphs on those four vertices, fixing the anchors and ears. Each canonical graph leaves six anchor-anchor edges and sixteen anchor-contact edges arbitrary. For every assignment of these 22 bits, place the two ears opposite their respective anchor pairs. There are two relative orientations, and each of the four contacts can be on either shore or left free. The kernel checks that whenever the four local triangle counts are distinct and at least two, one of these 162 placements gives every pinned vertex two neighbors on the opposite shore. The predecessor’s pinned maximum-cut theorem extends it to a two-dominating set. [Canonical relabeling](TenOrbit.lean) · [Edge and score semantics](TenSemantic.lean) · [Table theorem](TenTable.lean) · [Graph transfer](TenProtected.lean)

The 11 × 2²² cases are bit-parallel. Each of the 88 slices has 2¹⁹ bits. Every slice is a Lean equality of natural numbers proved by reflexivity. The files named TenBits contain two slices each, keeping peak memory bounded for independent replay. The relabeling and the transfer back to the original graph are kernel-checked separately. [Signal definitions](TenSignals.lean) · [Witnesses for the eleven isomorphism classes](TenCanon.lean)

## A sharp five-contact example

The 30-vertex graph in FiveData has exactly the stated profile. Its ears 27 and 28 have neighbors {0,1} and {2,3}. Its five triangle contacts are {4,5,6,7,8}, and its four anchor counts are 2, 8, 5 and 6. The graph has M = 5 and three double contacts. Vertex 29 is isolated. These values fall outside the predecessor’s exposure thresholds and its listed cap of six for the maximum anchor score at this exposure. [Adjacency matrix](FiveData.lean) · [Full triangle-count verification](FiveScores.lean) · [Profile](FiveWitness.lean)

Let K contain the two ears, their four anchors and their five contacts. A protected placement is a pair of disjoint vertex sets covering both ears with every placed vertex having two neighbors on the opposite shore. **The minimum number of vertices outside K required by any protected placement is exactly one.** To see the obstruction, pin ear 27 on the left. It forces 0 and 1 to the right. Inside K, vertex 0 needs 4 or 5 on the left. The neighbors of 4 inside K are exactly 0 and 5, and those of 5 are exactly 0 and 4. Placing either on the left forces the other to the right with only one opposite neighbor. Interchanging shores gives the same contradiction. [Lower bound and explicit placement](FiveLocal.lean) · [Exact minimum](FiveWitness.lean)

One outside vertex, 9, suffices. Take shores {0,1,2,3,9} and {27,28,4,6,7}. The graph itself satisfies the catalogue inequality. The set {0,3,4,6,8,10,13,15,16,21,23,24,27,28,29} two-dominates it. This example establishes a limit on cuts confined to K. [Two-dominating set](FiveWitness.lean)

## A cut criterion for larger T

Start with the four anchors on the left and the two ears on the right. Add every unassigned vertex having at least two left neighbors to the right, then add every remaining unassigned vertex with at least two right neighbors to the left. Iterate. The theorem `growing_anchors` says that once every anchor has a second right neighbor, the catalogue inequality follows. This criterion has no upper bound on T. On the example above, an anchor still has exactly one right neighbor after round one, and all four have at least two after round two. The result gives a sufficient condition. Its termination with all anchors covered remains unproved in general. [General iteration theorem](GrowingCuts.lean) · [Checked rounds on the example](FiveLocal.lean)

## Reuse and replay

The predecessor FourFront package supplies the profile, definitions, rank bounds, truth-word semantics and pinned maximum-cut argument. Its frozen source archive has SHA-256 `85a117e659987e07a1ece9403f376706a2eb12216c31c960c3085f4c6c44a61e`. Its shared-neighbor predecessor is public. [Shared anchors at revision 7d2af907](https://github.com/vjdad4m/maths/tree/7d2af907520e1df2e80b5d30d7238101560bec0f/graffiti-384b-shared-anchors)

For the shared workspace, enter the directory containing this file and run

```sh
python3 -B replay.py --checked ../graff384b-fourpins29-astra/StrictFour.log
```

For an extracted package elsewhere, set the installation paths. A cold build from the 272 included Lean files uses

```sh
CONTACT4_LEAN_BIN=/absolute/path/to/lean-4.19.0-linux/bin \
CONTACT4_MATHLIB=/absolute/path/to/mathlib4-4.19.0 \
python3 -B replay.py --cold
```

The tested replay used Lean 4.19.0 commit 6caaee842e94 and Mathlib v4.19.0 commit c44e0c8ee63ca166450922a373c7409c5d26b00b. It compiled all 67 extension modules synchronously, with warnings as errors. It checked all 272 source digests and the 205 object digests from the frozen FourFront replay. All 123 reported theorem dependencies are among propext, Classical.choice and Quot.sound. The checked-predecessor transcript accompanies the package. [Replay](replay.py) · [Transcript](StrictTen.log)

[Complete pinned Lean sources](proof-sources.zip). Extract the archive and use its replay script.
