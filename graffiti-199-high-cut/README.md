# Graffiti.pc #199 — all-high three-cut reduction

The starting case has vertex connectivity at least three, largest induced tree order at most five, and no Hamiltonian path. Its minimum-order hypothesis is `SmallerAtThree` from the published cubic-contraction package. Cubic vertices form an independent set. The published crossing reduction turns any failure of surviving-edge crossing into a three-vertex cut whose vertices have degree at least four, with two distinct components of order at least three.

## Main result

`Graffiti199Depleted.Catalogue.LargeCrossingFailure.traceable_of_order_le_nine` only needs the crossing witness, three-connectivity, the induced-tree bound, and order at most nine. It gives a Hamiltonian path. The separator and distinguished components already account for nine vertices, so in this order range those two components have order three and cover all survivors. Each is a triangle or an induced three-vertex path. Two triangle components use the existing splice. A triangle and a path use a Hall attachment on the triangle and the at-least-two port contacts at each endpoint of the path.

For two three-vertex path components, an incompatible route on each side would require both to use the same unordered port pair. Neither endpoint on either side can then see the third port, since its opposite endpoint has at least two port contacts. Each of the four endpoints consequently sees both ports in the pair. The third port has degree at least three and can see at most the two path middles on the two sides, so one port in the pair is adjacent to it. That port and the five vertices it sees induce a six-vertex star. The induced-tree budget rules this out.

`order_ge_ten_of_crossing_failure` transfers the theorem to the published minimum-order independent-cubic reduction. The general conjecture and the crossing-failure case from order ten onward remain open here.

## Shore interface

- `CubicDeletion.lean` proves `deletion_preconnected_with_cubic`, `connectivity_after_cubic_delete`, `traceable_after_cubic_delete`, and `all_ports_contact_components_after_cubic_delete`. If a cut of size at most three contains a cubic vertex, the earlier edge-to-edge crossing result connects all nonisolated survivors. An isolated survivor would itself be cubic with all three deleted vertices as neighbors, contrary to independence of the cubic vertices. Hence deleting just the cubic vertex preserves three-connectivity, and the exact induced deletion has a spanning path by minimum order. Deleting another three-vertex set after that forces every remaining component to contact each of its three ports.
- `CubicShorePacking.lean` and `HighCutProfile.lean` prove `cubic_shore_has_internal_flank`, `nonneighbor_on_cubic_shore`, and `high_cut_and_clique_shores_of_crossing_failure`. An original cubic vertex's neighbors are internal on any Hamiltonian path of its deletion and have nonneighbors of the cubic vertex on both flanks. On its original side, the number of cubic neighbors there equals the number of nonneighbor ports. Distinct internal positions need strictly more distinct flanks, so at least one flank is an internal nonneighbor. In particular no nontrivial clique component of a three-cut contains a cubic vertex in this minimum-order branch.
- `ShoreHall.lean` proves `shore_hall`, `shore_distinct_attachments`, and `LargeCrossingFailure.distinct_attachments`. For a subset of the ports, a hypothetical attachment deficit gives a deletion of fewer than three vertices which separates the surviving portion of the side from an exterior survivor. Mathlib's finite Hall theorem converts the resulting inequalities to three distinct contacts on each large side.
- `ShoreRouting.lean` defines `ShoreRoute` and proves `traceable_of_compatible_shore_routes`, `traceable_of_routable_and_clique_shores`, and `traceable_of_three_vertex_path_and_clique_shores`. Each route spans its side with specified terminal attachments. The splicing rule requires two different unordered port pairs, and its graph-cover hypothesis requires exactly two components after the cut.
- `TwoShortShores.lean` proves `traceable_of_two_three_vertex_path_shores`. This theorem and the assembled order theorem do not use minimum order or cubic independence.

## Routing witness

`RoutingWitness.lean` checks a traceable nine-vertex graph of connectivity exactly three and induced tree order at most five. Ports 0 and 1 are universal. After deleting the three ports, vertices 3–4–5 form a path and 6,7,8 form a clique. Port 2 sees only vertex 4 on the path side. Both path endpoints have degree three and the cubic vertices are independent. The Hall certificate holds on both sides. The path side supports exactly the pair {0,1}; the clique supports every pair. An explicit Hamiltonian path is 3–4–5–0–6–7–8–2–1. The witness limits the inference from Hall to prescribed routing.

The one-terminal domain on vertices 2,3,4,5 has a missing-edge degree sum below its order for every missing edge (`no_rooted_ore_step`). The threshold in the published `Graffiti189Ore.rooted_closure_one` is therefore unavailable in this deficient profile. The module with small clique routes from #189 was compared with the existing #199 `Traverses.clique`; the latter already has the exact endpoint and degree-free interface. The terminal-pair bookkeeping uses the same idea as the Kelmans terminal-domain analysis. No results about P₃-factors are needed.

- [Published cubic-cut reduction](https://github.com/vjdad4m/maths/blob/main/graffiti-199-mixed-cubic-cut/MixedCutReduction.lean)
- [Published crossing-cut package](https://github.com/vjdad4m/maths/tree/main/graffiti-199-crossing-cut)
- [Root-preserving #189 Ore closure](https://github.com/vjdad4m/maths/blob/fa1b2f88bf886ec92bd1288a016d087272766be9/graffiti-189-complete-degree-four/src/OreClosure189.lean)
- [Kelmans terminal-domain construction](https://github.com/vjdad4m/maths/blob/main/kelmans-three-shores/src/ThreeTerminalDomain.lean)

## Replay and provenance

In the shared workspace, run:

```sh
bash graffiti-199-high-cut/replay.sh /path/to/maths
```

With an independent public checkout, pass the repository root and set `GRAFF199_MATHLIB` to the built Mathlib checkout. If the Lean 4.19.0 executable is not already on PATH, set `GRAFF199_LEAN_BIN` to its bin directory. The script checks Lean 4.19.0 and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`, then rebuilds all project dependencies in source order with warnings as errors. It checks each SHA-256 before compiling. The 55 dependency sources are public and their Git blobs were matched against the workspace snapshots. `PublishedSources.tsv` has their paths, hashes, and direct imports, `PublicBlobAudit.tsv` records the live blob check, and `SourceManifest.tsv` orders and pins the new modules.

The headline theorems and witness were audited with `#print axioms`. Their project-level dependencies are the standard `propext`, `Classical.choice`, and `Quot.sound`. The deletion-path lift alone uses only `propext` and `Quot.sound`. Concrete witness propositions use kernel `decide`.
