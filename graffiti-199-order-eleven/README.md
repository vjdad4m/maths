# Graffiti.pc #199 — order-eleven three-cut progress

The frozen starting point is the [order-ten package at 53f2c8b7](https://github.com/vjdad4m/maths/commit/53f2c8b7).

## Checked results

`OrderElevenGeometry.lean` proves `LargeCrossingFailure.cover_of_minimum_at_order_eleven` and `order_eleven_crossing_failure_two_shapes`. An order-eleven minimum-order counterexample in the independent-cubic crossing-failure branch has an all-high three-cut whose surviving graph consists of exactly two components of orders **3 and 5** or **4 and 4**. The theorem derives the two-component condition using the published exclusion of surviving two-vertex components and the new spanning-path constructions for the 3+4+1 and 3+3+1+1 cuts.

- `StarContacts.lean` shows that at each port the sum of two independently chosen sets of independent contacts, one in each large component, plus the number of outside singleton components is at most four. Otherwise the port is the center of an induced six-vertex star. One singleton forces a port's contacts to form a clique in at least one side, and two singletons force them to form a clique on both sides. In the two-singleton case, any two distinct same-side vertices which each see at least two ports must be adjacent. With two nonempty sides there are at most two outside singletons.
- `StarContacts.lean` also locates an induced claw at a port whenever one side is a three-vertex path. Its ends share a port because each sees at least two. The third leaf is a contact on the opposite side.
- `TwoSingletons.lean` proves traceability for the 3+3+1+1 split. The path-shore exclusion forces both 3-vertex components to be cliques. Hall supplies the compatible routes and the singletons go at the two ends.
- `OneSingletonRoutes.lean` glues a three-vertex path, a singleton and any supported opposite route. A blocked ordinary splice forces shared endpoint contacts on the path; a split visit to that component supplies the path.
- `ClawSingleton.lean` handles an opposite claw, and proves traceability for the 3+4+1 split. If the three-vertex path has shared endpoint contacts, each of the two shared ports sees at most one independent claw leaf. This is insufficient to meet all three leaves, which each have at least two port contacts.
- `TwoComponentObstructions.lean` shows that a 3+5 nontraceable split cannot have a supported route on the five-vertex side, and a 4+4 nontraceable split cannot have a clique side. The first theorem works for any opposite size.
- `OrderTwelveSingletons.lean` proves traceability for the specific order-twelve split 3+4+1+1. More generally a claw side is excluded whenever there are two distinct singleton components and another nonempty side, since any two claw leaves each see at least two ports and are nonadjacent.

## Checked routing limitation

`RoutingLimitWitness.lean` verifies the explicit 11-vertex graph encoded by adjacency rows `[1662,1525,987,53,15,11,1927,326,198,69,67]`. The cut is `{0,1,2}`, with distinct surviving components `{3,4,5}` and `{6,7,8,9,10}`. Lean checks connectivity exactly three, tree number at most five, that the cut has degree at least four at all three ports, independent cubic vertices, an induced claw and an independent five-set. The graph has the Hamiltonian path `0–4–3–5–1–7–8–2–9–6–10`. Its five-vertex side cannot span a path at any endpoints, so every global Hamiltonian path visits that side in at least two intervals. This proves a limitation of the one-interval routing template.

## Computational census

Run `bash graffiti-199-order-eleven/replay_census.sh`. The C++ enumeration treats the three ports as labeled. Each connected internal graph is represented up to vertex relabeling, and its attachments are represented up to internal graph automorphisms. For each side it retains all attachments satisfying the minimum-degree condition, independence of cubic vertices within the side, and the Hall necessary condition. Pairs are filtered by the independent-contact star bound, and the full degree of the cut is checked after including port edges and all singletons.

The routing test is exact. A path orders the three ports in one of six permutations and leaves four intervening intervals. Each nonempty interval belongs to one component. A local subset DP computes all ways each component can be partitioned into paths in specified intervals, with the required adjacent ports at their ends. The global assembly checks disjoint occupied intervals, allocates the singleton components, and checks each required cut edge between consecutive ports whenever the corresponding interval is empty. The census also tests a sample against an independent whole-graph subset DP.

| Order-eleven split | Labeled-port profiles after the stated filters |
| --- | ---: |
| 3+3+1+1 | 13,448 |
| 3+4+1 | 818,476 |
| 4+4 | 27,879,072 |
| 3+5 | 42,526,173 |

All 71,237,169 profiles admit Hamiltonian paths. The tables retain their labeled ports and can include isomorphic graph pairs. The census is computational evidence. Lean checks the reductions, the singleton splices, and the explicit routing witness. A Lean verification of the census for 3+5 and 4+4 remains open.

The optional `--order-twelve` census tests the 3+4+1+1, 4+4+1, 3+5+1 and 4+5 splits, also with no failures. Its scope is limited to exactly two nonsingleton components, each of order at most five. The case of a size-six component or three nonsingleton components is outside that census.

## Replay and provenance

Run `bash graffiti-199-order-eleven/replay.sh` from the repository checkout. It rebuilds all 75 published dependency files and eight new files from source after checking SHA-256, with Lean 4.19.0, Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`, and warnings as errors. The script uses the published source snapshots by default. For an independent checkout, pass its repository root as the first argument and set `GRAFF199_MATHLIB` to the built pinned Mathlib checkout. Set `GRAFF199_LEAN_BIN` if the pinned executable is not already on PATH.

`PublishedSources.tsv` and `SourceManifest.tsv` record the ordered source closure. The local order-ten package was preserved. The headline theorems use only `propext`, `Classical.choice`, and `Quot.sound`. The only finite Lean evaluations are kernel `decide` checks.
