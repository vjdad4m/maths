# A switch at a triangular ear for Graffiti.pc #384b

Ermelinda DeLaViña's January 2010 conjecture #384b asks whether every connected graph of order `n>2` has a two-dominating set of size at most `n−⌈t/2⌉`, where `t` counts the distinct numbers of triangles incident to a vertex. A vertex outside a two-dominating set must have at least two neighbors in the set. Write `q` for the number of vertices of degree at least two. This package treats the minimum quota `q=t−1`. At this quota each nonleaf has a distinct, positive triangle count. [Official catalogue](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/index.html) · [Catalogue entries](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json)

## Original graph theorems

Suppose a degree-two vertex `e` has neighbors `r,b` and the edge `rb` is present. Let `S` be all nonleaves except `r,e,b`, and let `C` be the vertices in `S` adjacent to both anchors `r,b`. All degrees and triangle counts below refer to the original graph.

* If `|C|≥5` and a vertex of `C` has degree three, the graph satisfies #384b. The other vertices of `S` have unrestricted degrees. [CubicFront.lean](CubicFront.lean)
* If every vertex of `S` has degree at least four, `|C|≥5`, and a vertex of `C` has degree four, the graph satisfies #384b. Under the same minimum-degree hypothesis, a degree-four vertex of `C` in at least five triangles suffices for *any* quota and any number of common neighbors. The formal statements allow arbitrary finite simple graphs. [QuarticFront.lean](QuarticFront.lean) · [HighScore.lean](HighScore.lean)
* For the previous rich-root problem, suppose a leaf is adjacent to `r`, all vertices of `S` have degree at least four, and `|C|≥5`. Set `T=N(b)∩S`. If `|T|>⌈|S|/2⌉` or some vertex of `T` has more neighbors in `T` than in `S∖T`, the graph satisfies #384b. The preceding release required degree at least five for its density argument. Here a failure with degree four would supply a common quartic, to which the switch applies. [dense_mate_four](QuarticFront.lean) · [Prior local theorem](https://github.com/vjdad4m/maths/blob/53bce2fb9709801ef1525cc398e6b68e7d043bb4/graffiti-384b-rich-root-exchange/LocalFrontier.lean)

## Why one vertex must block every switch

Retain the two anchors and omit the ear and two distinct members `v,w` of `C`. The earlier seeded cut on the remaining nonleaves implies that failure forces a further exterior vertex `x` satisfying

```
degree(x) + |N(x) ∩ {r,b}| < 3 + |N(x) ∩ {v,w}|.
```

For a fixed cubic `v`, such a vertex must be cubic, miss both anchors, miss `v` and meet `w`. A cubic meeting `v` would be forced to share triangle count two with `v`. All exterior cubics have triangle count two or three, so at most one remote cubic is available after accounting for `v`. Varying `w` makes the same remote cubic adjacent to every vertex of `C∖{v}`. At five common vertices its degree is too small. [EarSwitch.lean](EarSwitch.lean) · [CubicScores.lean](CubicScores.lean) · [CubicFront.lean](CubicFront.lean)

For a common quartic `v` when all exterior degrees are at least four, the obstructing vertex must be quartic, miss both anchors, and meet *both* `v,w`. There is at most one such low-degree neighbor of `v`. If there were two, say `x,y`, the neighborhood of `v` would be `{r,b,x,y}`. Its only possible link edges would be `rb` and `xy`. The ear already has count one, forcing `xy` and giving `v` count two. Then `x,y` have distinct counts at least three. Each of the edges `vx,vy` lies in only one triangle. The local triangle lemma shows that this forces one of `x,y` to have degree at least five. Thus the same remote quartic would have to see all of `C`. [QuarticTriangle.lean](QuarticTriangle.lean) · [SparseQuartics.lean](SparseQuartics.lean)

If the common cubic has triangle count three, its third neighbor is automatically in `C`. Any failure then needs a remote cubic of count two. If a common quartic has triangle count at least five, at most one pair in its neighborhood is a missing edge. Consequently it has another neighbor in `C`, and no neighbor of it can miss both anchors. This gives the quota-independent result above. [HighScore.lean](HighScore.lean)

## Checked examples and scope

A connected 15-vertex graph with 14 nonleaves and 15 counts has a leaf at `r` and six members of `C`. Lean verifies both that the earlier residual-palette and weighted-degree tests fail for this ear and that the new quartic theorem proves the catalogue bound. Two connected 13-vertex graphs with 12 nonleaves and 13 counts realize the respective cubic and quartic blocker neighborhoods at `|C|=4`. Each has an explicit two-dominating set of size five, within the catalogue bound of six. This shows why the single-blocker degree count alone cannot exclude four contacts. The general minimum-quota rich-root case remains open. [SwitchExamples.lean](SwitchExamples.lean)

The proof reuses `Repair.seeded_cut` and the rich-root release's `low_degree_obstruction`. The other rich-core release's donor-pair results count possible blockages separately for each pair. The new step uses distinct original triangle counts to identify one blocker common to every switch with a fixed low-degree vertex. The ArticulationRoot theorem concerns disconnection after deleting the root. The ear switch needs no disconnection. [Rich-root release](https://github.com/vjdad4m/maths/tree/53bce2fb9709801ef1525cc398e6b68e7d043bb4/graffiti-384b-rich-root-exchange) · [Ear-donor-pairs release](https://github.com/vjdad4m/maths/blob/8b6a808f3dfe98d850051ec4a422520a19b16952/graffiti-384b-rich-core-ear-kernel/README.md)

## Strict replay

The archive contains the eight new Lean modules, all 87 transitive project sources, a replay script, the strict transcript and SHA-256 manifests. The predecessor source archive is authenticated by SHA-256 `54ecdc21e852e91cd0cf8832eba94a881e2cd424f53e549190c3a0a24d8cb90a`. The transcript records a serial rebuild of the eight modules from the extracted delivery at Lean 4.19.0 commit `6caaee842e94` and Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`, using previously checked, hash-matched predecessor objects. The verifier treats warnings as errors, rejects unchecked proof shortcuts and validates every new axiom report against `propext`, `Classical.choice` and `Quot.sound`. [Replay script](replay.py) · [Transcript](StrictQuartic.log) · [Delivery manifest](DELIVERY.sha256)

From the extracted directory in the shared workspace run

```bash
ws=/workspace/scratch/7efa613b1c05
export QSWITCH_LEAN_BIN="$ws/graff384b-codex/.deps/lean-4.19.0-linux/bin"
export QSWITCH_MATHLIB="$ws/graff384b-codex/.deps/mathlib4"
python3 -B replay.py --checked "$ws"
```

For an independent full source rebuild, set the two environment variables to compatible installations and run `python3 -B replay.py --cold`.

[Complete pinned Lean sources](proof-sources.zip). Extract the archive and use its replay script.
