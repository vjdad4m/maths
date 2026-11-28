# Graffiti.pc #384b for 29 triangle counts and 29 nonleaves

For every finite simple graph with **29 distinct vertex triangle counts and 29 vertices of degree at least two**, the two-domination number is at most **the order minus 15**. Isolated vertices and leaves are allowed. A two-dominating set contains two neighbors of every vertex outside it. The January 2010 catalogue entry asks whether every connected graph on n > 2 vertices satisfies γ₂(G) ≤ floor(n − |T|/2), where T is the set of incident triangle counts. The theorem here allows disconnected graphs as well. [Formal theorem and corollary](CompleteFourRoots.lean) · [Invariant definitions](prior/Proof384b.lean) · [Ermelinda DeLaViña’s Graffiti.pc catalogue](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/index.html) · [Catalogue data, entry 384b](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json)

The new case has exactly 27 vertices of degree at least three. The two remaining nonleaves have degree two. The theorem `exact_profile` proves the catalogue bound in this case with no hypotheses about specific vertices, degrees of their neighbors, triangle contacts or connectedness. The corollary `twenty_nine_nonleaves` combines this with the earlier theorem for at least 28 high vertices and the elementary bound of two more triangle counts than high vertices. The scope of the result is the 29-type, 29-nonleaf profile. [New proof](CompleteFourRoots.lean) · [Earlier high-vertex bound](prior/Remaining29.lean)

## Why two leftover roots cannot coexist

Suppose the bound fails. Earlier reductions give four different high neighbors of the two degree-two vertices. Call them roots. All high vertices have distinct triangle counts of at least two. At most fourteen high vertices outside the roots occur in a root triangle, and some root belongs to at least thirteen triangles. The earlier fork lemma implies that a root cannot see both roots of the opposite degree-two vertex. Consequently each root has at most two root neighbors, and the four roots span no triangle. [Earlier reductions](prior/FiveFront.lean) · [Fork lemma](prior/ForkClosure.lean) · [Root graph](RootPairs.lean)

Pin all roots on one side of a cut and both degree-two vertices on the other. A contact seeing two roots can be pinned opposite them. A root whose private contacts contain a three-vertex path can be protected by alternating the sides along the resulting four-cycle. A root is called weak when neither repair applies. Apart from its possible triangle through a degree-two vertex, its triangles use disjoint pairs of private contacts. If just one weak root remains, a free triangle repairs it. The repair uses the four-clique around a cubic vertex with triangle count three and the uniqueness of a cubic blocker of triangle count two. [Private cuts](WeakRootPatch.lean) · [Private pairs](PrivateLinks.lean) · [Free-triangle repair](FreeTriangle.lean)

A root with score at least thirteen needs at least four contacts. These contacts are disjoint from the private pairs at every weak root. Since at most fourteen contacts are available, three weak roots with distinct scores of at least two would use too many. A failure therefore has exactly two weak roots. If their scores are s and t, at least 2(s+t) contacts are required. This already rules out at most nine contacts. [Two-root reduction](PrivateFront.lean)

Select a private pair at the lower-scoring weak root and two private pairs at the higher-scoring root. The six chosen vertices are high. For each selected vertex x, consider the high neighbors outside the four roots and the six selected vertices. If two such neighbor sets meet, the common vertex supplies an alternating four-cycle at one root or a four-edge path between the two roots. One repair leaves the other root’s private triangle available. Thus a failure forces all six neighbor sets to be pairwise disjoint. It also forces every triangle at x other than its root-and-mate triangle to use two vertices of its own neighbor set. [Selection](Carriers.lean) · [Alternating paths](PinBoard.lean) · [Triangle bound](SatelliteBound.lean)

Write d for the size of one such neighbor set. The score of x is at most 1+binom(d,2). The six scores are distinct and at least two. All six sets have size at least two, at least five have size at least three, and at least one has size at least four. Disjointness therefore requires at least 18 vertices. Only 27−4−6=17 are available. [Counting argument](SatelliteCount.lean) · [Contradiction](SatelliteBound.lean)

## Source and replay

The source closure uses the published maximum-cut completion and private-root reductions, and the frozen six-contact package’s one-vertex exchange and fork lemmas. The predecessor archive has SHA-256 `c636e35dfa3c35123bd9989dd184726272af943d6ec247eba94866bf3935d7ec`. All results above follow by structural arguments. [Shared research repository](https://github.com/vjdad4m/maths) · [Imported source manifest](PREDECESSORS.sha256) · [New source manifest](SOURCES.sha256)

Unpack the archive and run this from the directory containing `replay.py`. In the shared workspace, the following command authenticates the imported Lean objects and recompiles every new module with warnings as errors.

```sh
w=/absolute/path/to/predecessor-checkout
GAP_LEAN_BIN="$w/graff384b-codex/.deps/lean-4.19.0-linux/bin" \
GAP_MATHLIB="$w/graff384b-codex/.deps/mathlib4" \
python3 -B replay.py --checked "$w"
```

For a portable source rebuild, use Lean 4.19.0 at `6caaee842e94` and Mathlib 4.19.0 at `c44e0c8ee63ca166450922a373c7409c5d26b00b` with matching Mathlib objects. Set the two environment variables to those installations and run `python3 -B replay.py --cold`. The recorded replay used the checked-object mode. It scans the complete project import closure for placeholders and additional axiom declarations, and audits the printed axioms of the new theorems. [Replay script](replay.py) · [Strict transcript](StrictProfile.log)

[Complete pinned Lean sources](proof-sources.zip). Extract the archive and use its replay script.
