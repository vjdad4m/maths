# Graffiti.pc #384b with two private neighbors of an anchor

In the exact profile there are 29 distinct vertex triangle counts, 29 vertices of degree at least two and 27 vertices of degree at least three. The two degree-two vertices are called ears. Their four distinct high neighbors are the anchors. The pool consists of the other 23 high vertices. A contact is a pool vertex on a triangle through an anchor. The catalogue bound in this profile is γ₂(G) ≤ |V(G)| − 15. [Ermelinda DeLaViña’s Graffiti.pc catalogue](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/index.html) · [Conjecture data, entry 384b](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json)

## A structural case of the conjecture

Let the ears have neighbor pairs {a,b} and {c,d}. Suppose b is adjacent to both c and d. Suppose a has two distinct pool neighbors x and y such that each sees only a among the anchors and neither sees a triangle contact outside {x,y}. Then the catalogue inequality holds. The numbers of contacts and the four anchor triangle counts are unrestricted. Other edges may be present. The theorem applies to finite simple graphs of arbitrary order in the stated profile. [Graph theorem](ForkPatch.lean)

A protected cut is a pair of disjoint pin sets in which each pin already has at least two neighbors pinned on the opposite side. The theorem starts with {a,b,second ear} opposite {first ear,c,d}. Only a may still need a second neighbor. More generally, the same proof starts from any pair of disjoint sets containing both ears whose only possible deficit is one missing opposite neighbor at a. The pins used at the start must avoid the pool. There is a protected cut extending these sets with at most three vertices outside the two ears, the four anchors and the two ports x and y. If x and y are contacts, this also bounds the pins outside the entire contact patch by three. [Unconditional existence in the exact four-anchor profile](ScoreFreePatch.lean) · Conversion to two-domination (archive: `PrivatePorts.lean`)

## Why three vertices suffice

Put S = {x,y}, let W be the 21 other pool vertices, and let U consist of the vertices of W that see S. A vertex of W adjacent to both ports completes the cut using one W-vertex. If some vertex z of W sees two distinct members of U, place those two members on the deficient anchor’s side and put z and their chosen ports opposite. This completes the cut using at most three W-vertices, even when the two chosen ports coincide. Explicit placements (archive: `PortFrames.lean`)

Assume neither placement is available. Every W-vertex then sees at most one port and at most one member of U. For each port its triangles with both partners in W have disjoint pairs of partners. Pairs from different ports have disjoint endpoints as well. If their total number is m, then |U| ≥ 2m. Counting edges from U into W gives at most |W| incidences, including both orientations of an edge internal to U. Matching and incidence count (archive: `PortCount.lean`)

At most one triangle per port is lost on restriction to the pool. Its other vertices must be the deficient anchor and the other port. In the absence of the one-vertex repair, the triangles wholly in the pool have both partners in W. Each boundary vertex’s own triangle partners lie in the pool, since none of those boundary vertices is an anchor-triangle contact. Maximal triangle diversity makes all high scores distinct and at least two. These facts imply 6m ≤ |W| + 2. Consequently m ≤ 3, and the port scores must be 2 and 3. Triangle localization (archive: `PrivatePatch.lean`) · Degree and score count (archive: `PortRank.lean`)

Every member of U must now have score at least four. If it has r neighbors in W, its score is at most C(r,2) + 1. The extra triangle must use its unique port neighbor and its unique neighbor in U. Hence r ≥ 3 and at most one member of U can have r = 3, because only one can have score four. Counting incidences again gives 4|U| ≤ |W| + 1. But the two port scores already force m ≥ 3 and |U| ≥ 6, giving 24 ≤ 22. This proves the three-vertex bound without specifying the deficient anchor’s score. The rank inequalities and cut constructions are independent of graph order. Refined link bound (archive: `SharpPortRank.lean`)

The residual theorem combines the resulting forbidden two-port configuration with the published weighted five-point selection inequality. A hypothetical failure defeats every admissible weighted test. For every pair of candidate neighbors in the displayed ear configuration it also has an edge from one of them to another anchor or to a contact outside the pair. The general six-contact case is still open. [Combined residual](MixedResidual.lean)

## Three is sharp, including when all nonleaves lie on triangles

The 30-vertex witness is connected. Both ears have score one, and its only triangle-free vertex is a leaf. It has 29 nonleaves, 27 high vertices, 29 triangle counts and T = M = 6, where M counts pool vertices with any neighbor outside the pool. Its four anchor scores are 2, 13, 9 and 10. The five-point test requires all six contacts. The minimum number of pins outside the twelve-vertex patch required by any protected cut covering both ears is exactly **three**. One such cut has shores {0,1,28,10,13} and {27,2,3,4,5,18}. The three external vertices are 10, 13 and 18. An explicit set of nine vertices two-dominates the graph, giving γ₂ ≤ 9 and a catalogue bound of 15. [Full adjacency matrix and kernel-checked witness](PositiveExample.lean)

For the lower bound, with only two exterior pins an exterior vertex can get at most one opposite neighbor outside the patch. Each exterior neighbor of private port 4 or 5 sees only that port inside the patch. Every exterior neighbor of such a vertex can also see at most that same port inside the patch. The two exterior endpoints would therefore need that port on opposite shores. Removing both options leaves the deficient anchor unable to protect its ear. Two-pin obstruction (archive: `ThinOutside.lean`) · Private-triangle lower bound (archive: `PrivateLower.lean`)

A second connected witness has order 29, T = M = 6 and the very same induced twelve-vertex graph as the preceding five-point obstruction. Its exterior changes the exact minimum from one to three. Its two-domination number is at most eight. The 30-vertex witness above also certifies sharpness in the remaining positive-nonleaf case. Equality of the patches and the five-point tests (archive: `SamePatch.lean`) · Order-29 cut minimum (archive: `ThreeSharp.lean`) · [Published triangle-free-nonleaf theorem](https://github.com/vjdad4m/maths/commit/6c3123cd92e5b51d023054ebe2f7c88ca58ce871)

## Reuse and replay

The frozen five-choice source archive has SHA-256 `0ea12caaa8d208d2e0a3cac781f64dd0e261f9ac655db1352de4b5fa2920019a`. The new proof reuses the maximum-cut completion, the high-degree triangle-rank data, the restricted link graphs, the weighted selection criterion and the ordered-pair counter for the finite examples. The private-neighbor bound counts root and return incidences directly in an irregular graph. Zhang’s Lemma 11.2 records the regular triangle-degree bound of Hak, Kozerenko and Serdiuk. [Frozen repository predecessor](https://github.com/vjdad4m/maths/tree/1964ad44240bfe0a074a5514c380d29b20060459/graffiti-384b-five-choice-tests) · [Earlier weighted sampling](https://github.com/vjdad4m/maths/tree/b33aad93ffcaab8f8c9e21a6fc56592675782f6f/graffiti-384b-30-nonleaf-complete) · [Zhang, Section 11.2](https://borowiecki.dev/pdf/2611.10557)

In the shared workspace run from this directory

```sh
python3 -B replay.py --checked ..
```

The source-only archive includes the complete project import closure. To compile the predecessors as well, extract the archive and run

```sh
PORT_LEAN_BIN=/absolute/path/to/lean-4.19.0-linux/bin \
PORT_MATHLIB=/absolute/path/to/mathlib4-4.19.0 \
python3 -B replay.py --cold
```

The replay pins Lean 4.19.0 at `6caaee842e94` and Mathlib v4.19.0 at `c44e0c8ee63ca166450922a373c7409c5d26b00b`. It runs synchronous elaboration with warnings as errors, checks the source and object digests used in checked mode and audits printed theorem axioms. Replay (archive: `replay.py`) · Strict transcript (archive: `StrictPorts.log`)

The extracted-package replay passed all 16 new modules and 39 printed axiom reports. It matched 360 predecessor source and object digests. After an interrupted run, ten completed extracted modules were resumed with matching source and object hashes. The remaining six were rebuilt in the final extraction. All sixteen extracted objects match a separate worktree compilation byte for byte. The cold predecessor rebuild was not run in this check. Object comparison (archive: `PackedObjects.log`)

[Complete pinned Lean sources](proof-sources.zip). Extract the archive and use its replay script.
