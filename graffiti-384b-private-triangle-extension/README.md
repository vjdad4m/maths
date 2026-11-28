# Private triangles and degree-two vertices in Graffiti.pc #384b

Let `t` count the distinct numbers of triangles incident to a vertex, `q` count vertices of degree at least two, and `h` count vertices of degree at least three. Ermelinda DeLaViña’s January 2010 catalogue asks whether every connected graph with `n>2` satisfies `γ₂(G) ≤ n − ⌈t/2⌉`. A two-dominating set gives every vertex outside it at least two distinct neighbors in the set. All results below allow arbitrary finite simple graphs and count a realized zero in `t`. [Official catalogue](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/index.html) · [Entry 384b](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json)

## A necessary configuration at every diversity

Call a degree-two vertex an ear and a vertex of degree at least three high. Let `E` be the ears and `W` the union of their neighborhoods. Suppose `t≤q` and `E` is independent. In any counterexample there is an `a∈W` adjacent to exactly one vertex of `E` such that **every triangle at `a` avoiding `E` lies wholly in `W`**. At most one triangle at `a` uses an ear, so its triangle count is at most one plus its count in the induced graph on `W`. This gives a check on individual anchors even when their neighborhoods overlap, `W` contains triangles or high-vertex scores repeat. [Graph-level theorem](PaletteException.lean) · [Internal triangle count](TrappedAnchor.lean)

Two consequences give the catalogue bound.

* If `t≤q`, `t=h+2`, every ear neighbor is high, and the induced graph on `W` is triangle-free, the bound holds for any number of ears. The maximal-diversity lemma in the shared repository gives each high vertex at least two triangles, contradicting the necessary configuration. [Triangle-free anchors](TrappedAnchor.lean)
* Suppose exactly two vertices have degree two, they are nonadjacent and their neighborhoods are disjoint. If `t≤q` and all four neighbors belong to at least two triangles each, the bound holds, including when `W` contains triangles. In particular the full four-distinct-high-neighbor case holds at **every `t=q`**. In that case `h=t−2` supplies the score hypothesis. A triangle on the four anchors produces a vertex joined to both anchors of the other ear. Orienting the two pairs oppositely protects three anchors and leaves a single repair. [Two-ear theorem](TwoEarCompletion.lean) · [Opposite orientations](DisjointEarFork.lean)

These statements apply directly to odd `t`, including values below 29. The independent-ear result requires `q≥t`. The minimum nonleaf quota `q=t−1`, adjacent ears, and trapped-anchor configurations beyond the proved corollaries remain outside this reduction. Apply the hypotheses in the graph under consideration, since attaching a leaf can change which vertices have degree two. The repository already contains the full 29-count theorem and a reduction to a leaf attached to a connected positive triangle core with an ear. [Published index at revision 539b10a0](https://github.com/vjdad4m/maths/blob/539b10a0feb429b8f38af60969066ecc630c6461/README.md) · [Leaf-core reduction](https://github.com/vjdad4m/maths/tree/539b10a0feb429b8f38af60969066ecc630c6461/graffiti-384b-missing-one)

## Why the private triangles give an extension

Start with disjoint pinned shores `P,Q`. All pins already have two opposite neighbors except for a set `D⊆P`; each member `a∈D` has at least one opposite neighbor. For each `a` reserve a triangle `a,x,m` with `x,m` unpinned. The free pairs for different roots must be disjoint. Suppose no triangle has two unpinned vertices both belonging to just that triangle. Then there are enlarged shores that preserve every initial pin and give *every* pinned vertex two opposite neighbors. The graph extension itself has no quota, parity, degree, or injectivity hypothesis. [Frame and shift](TriangleFrame.lean) · [Simultaneous extension](PrivateTriangleExtension.lean)

Choose a failing configuration maximizing the number of pins. A reserved vertex seeing a different old pin allows an alternating path of length two or three. An edge between two reservations repairs both roots. A second triangle at `x` meeting `a` or `m` gives a four-cycle. Otherwise its other two vertices are outside every reservation and both shores. Put `x` on the left and `m` on the right. The old root is repaired, `m` is protected, and the second triangle is a free reservation for the new gap `x`. This enlarges the pinned set. Thus both vertices of every surviving reserved pair would have triangle count one. A seven-vertex square and triangle joined by a bridge certifies that such a pair can prevent the cut extension. It concerns only the extension lemma. [Short returns](TriangleReturns.lean) · [Kernel-checked sharpness example](ThinPairExample.lean)

For the catalogue application place the independent ears on the right and all their neighbors on the left. The earlier shared-contact and private-path construction supplies initial protected pieces. An anchor still deficient is adjacent to exactly one ear. Any triangle there avoiding the ears and extending outside `W` supplies a free pair private to that anchor. Outside the ears, two vertices of the same triangle with score one would both be high. Deleting one from the image of the high-vertex score map and adding zero gives `t≤h`, which already proves the catalogue bound by the high-vertex cut. This eliminates the thin-pair exception in any graph counterexample. [Ear-neighborhood construction](EarNeighborhood.lean) · [Palette argument](PaletteException.lean)

## Reuse and verification

The short alternating pieces, the initial assignment at weak roots, the high-vertex bound, and the completion of a protected cut come from the shared repository. The fork labeling and four-anchor enumeration adapt the earlier 29-specific proofs. The growing-reservation argument replaces the six-support count with a strict increase in the number of pinned vertices. The claim of verification concerns the named Lean theorems. [Earlier 29-nonleaf argument](https://github.com/vjdad4m/maths/tree/539b10a0feb429b8f38af60969066ecc630c6461/graffiti-384b-29-nonleaf-profile) · [29-count source closure used here](https://github.com/vjdad4m/maths/tree/539b10a0feb429b8f38af60969066ecc630c6461/graffiti-384b-diversity29-complete)

The bundle contains the nine new modules and all 370 imported predecessor modules, with source hashes and the checked workspace object map. The input archive was `graffiti-384b-diversity29-complete-source.zip`, SHA-256 `8ce848c153790a3e1b4938f40f4d11bd8eeee6d4752b65a7940c16df5678cf06`. Replay requires Lean 4.19.0, commit `6caaee842e94`, and a built Mathlib 4.19.0 checkout at `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The replay checks source hashes and the axiom reports and treats warnings as errors. [Replay script](replay.py) · [Recorded strict replay](StrictTriangle.log)

From the extracted directory in the shared workspace run

```bash
ws=/workspace/scratch/7efa613b1c05
export TRIANGLE_LEAN_BIN="$ws/graff384b-codex/.deps/lean-4.19.0-linux/bin"
export TRIANGLE_MATHLIB="$ws/graff384b-codex/.deps/mathlib4"
python3 -B replay.py --checked "$ws"
```

For a full source rebuild in another workspace, set the same two environment variables to the matching local installations and run `python3 -B replay.py --cold`. The recorded run rebuilds the nine new modules from their extracted sources after verifying predecessor objects against their frozen hashes.

[Complete pinned Lean sources](proof-sources.zip). Extract the archive and use its replay script.
