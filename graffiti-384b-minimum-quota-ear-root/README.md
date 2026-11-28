# Graffiti.pc #384b at the minimum nonleaf quota

**If a finite simple graph has fewer nonleaves than distinct vertex triangle counts, and some vertex in exactly one triangle has a leaf neighbor, then it satisfies Graffiti.pc #384b.** The score-one vertex may have arbitrary additional neighbors. Other leaves, unsupported edges, and disconnected graphs are allowed. [Main Lean theorem](RootedMinimumQuota.lean)

Write `t` for the number of distinct incident-triangle counts, including a realized zero, and `q` for the number of vertices of degree at least two. Ermelinda DeLaViña’s January 2010 catalogue asks whether each connected graph of order `n>2` has a two-dominating set of size at most `n−⌈t/2⌉`. Every vertex outside such a set has at least two neighbors in it. The earlier minimum-quota theorem shows that `q<t` forces `q=t−1` and that the scores on the nonleaves are positive and pairwise distinct. [Official catalogue](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/index.html) · [Entry 384b](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json) · [Minimum-quota lemma](prior/OddQuota384b.lean)

The published reduction leaves a single leaf attached to an arbitrary vertex of a connected positive triangle core containing a degree-two vertex of score one. At minimum quota the new theorem settles attachment at the score-one vertex. A counterexample in that quota must attach every leaf to a vertex with at least two triangles. The other root positions remain open in this argument. [Pinned index](https://github.com/vjdad4m/maths/blob/a067a39ef76278992069742b361b6abe83caa8c0/README.md) · [Leaf-core reduction](https://github.com/vjdad4m/maths/blob/a067a39ef76278992069742b361b6abe83caa8c0/graffiti-384b-missing-one/EarCoreReduction.lean)

## A prescribed edge in a protected cut

Suppose the endpoints of an edge `ab` have unequal positive triangle counts. Assume that all positive scores outside those endpoints are distinct and at least two. There are then disjoint sets containing `a` and `b`, respectively, in which every chosen vertex sees at least two vertices of the other set. Vertices of score zero are allowed, and other vertices may repeat an endpoint’s score. [Prescribed-edge theorem](PrescribedEdge.lean)

Orient the edge so that `a` has the larger count. Some triangle at `a` must avoid `b`, since both endpoints count the same triangles containing their edge. Let `S` consist of the vertices sharing a triangle with `b`. If every triangle at every vertex in `S∖{a}` passed through `b`, their distinct scores would all belong to the interval from two through `|S|−1`. That interval has fewer elements than `S∖{a}`. Thus a second neighbor `x` of `b` also has a triangle avoiding `b`. Place `a,x` on one shore and `b` on the other. The private-triangle extension, generalized to arbitrary initial pins, completes the protected cut. [Fiber counting](EdgeSpectrum.lean) · [Escape criterion](EscapingPins.lean) · [Prior simultaneous extension](https://github.com/vjdad4m/maths/blob/a067a39ef76278992069742b361b6abe83caa8c0/graffiti-384b-private-triangle-extension/PrivateTriangleExtension.lean)

## The extra omission

Let `eab` be the unique triangle at the vertex `e` adjacent to a leaf. Isolate `e` by deleting its incident edges. Among the other vertices, only `a,b` lose triangles, precisely one each. Their scores remain unequal and positive, and all remaining positive scores are distinct and at least two. The prescribed-edge theorem places `a,b` on opposite shores. A maximum cut extending these pins protects the other nonleaves because every unpinned nonleaf apart from `e` still has degree at least three. [Exact loss](SingleTriangleLoss.lean) · [Catalogue application](RootedMinimumQuota.lean)

For either choice of shore, omit its nonleaves other than `e`, and additionally omit `e`. The omitted vertex `e` sees the retained leaf and a retained anchor on the opposite shore. The two feasible omission sizes sum to `q+1=t`. One choice omits at least `⌈t/2⌉` vertices. [Shared omission](PivotWithLeaf.lean)

## Counterexample tests and sharpness

* Move the leaf of the published nine-vertex equality graph from vertex 8 to the unique score-one vertex 3. The resulting connected graph has `q=8`, `t=9`, and `γ₂=4`. The checked upper-bound set is `{0,4,6,8}`. Lean checks every smaller set. An exploratory calculation tested all eight leaf positions on this core and found no catalogue counterexample. The formal certificate concerns position 3. [Equality certificate](SharpEarRoot.lean) · [Original graph](https://github.com/vjdad4m/maths/blob/a067a39ef76278992069742b361b6abe83caa8c0/graffiti-384b-leaf-cuts/PairExample.lean)
* Add a new triangle at vertex 8 of the published ten-vertex rich core. The two new vertices each have score one, and all ten remaining vertices have distinct scores at least two. Placing the new edge across a protected cut would force vertex 8 onto both shores. This gives a counterexample to dropping the unequal-endpoint hypothesis in the edge theorem. [Checked obstruction](EqualEndpointExample.lean) · [Original rich core](https://github.com/vjdad4m/maths/blob/a067a39ef76278992069742b361b6abe83caa8c0/graffiti-384b-upper-example/UpperExample.lean)

## Replay

The source-only archive contains eight new modules and all 374 transitive predecessor modules. The frozen private-triangle source input has SHA-256 `c058f4f81553615740ab6564280ee6276b64bf5e697095f04e0dce83afb8bd41`. Replay uses Lean 4.19.0 commit `6caaee842e94` and Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. It checks source hashes, treats warnings as errors, and audits the printed axioms of each listed theorem. [Replay script](replay.py) · [Strict transcript](StrictEarRoot.log)

From the extracted directory in the shared workspace run

```bash
ws=/workspace/scratch/7efa613b1c05
export EARROOT_LEAN_BIN="$ws/graff384b-codex/.deps/lean-4.19.0-linux/bin"
export EARROOT_MATHLIB="$ws/graff384b-codex/.deps/mathlib4"
python3 -B replay.py --checked "$ws"
```

For a full source rebuild, set the same two variables to compatible local installations and run `python3 -B replay.py --cold`. The recorded run hash-verifies the old objects and compiles the new sources in order with a single Lean process at a time.

[Complete pinned Lean sources](proof-sources.zip). Extract the archive and use its replay script.
