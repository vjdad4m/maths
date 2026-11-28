# Universal-shore connectivity and terminal routing (#189, partial)

Write d=k+2. This delta builds on the checked [Hall linkage package](https://github.com/vjdad4m/maths/tree/85feab465e4dff5ce086a6de7fe041c69c0a5ca4/graffiti-189-hall-linkage) and older
exact-cut modules. It does not prove unrestricted #189. The geometric
instantiations below concern a high omitted root x of a longest path P with
two separated attachments and an omitted neighbor; A is its omitted closed
neighborhood, h=|A|, and B is the exact external cut of size k.

1. **Shore connectivity.** `UniversalCharge189` charges *all* distance-two
   cut vertices alongside internal nonneighbors and the opposite-shore
   Hall destinations. For v in A:
   `h + deg_G(v) + |D2(v) ∩ B| ≤ 2 deg_A(v) + d + 1`.
   `UniversalWideCut189` applies this to the closed neighborhood of v
   within one side of a cut of A; `ShoreConnectivity189` gives actual
   induced-graph connectivity after deleting X whenever `3|X|+4<h`.
   `StarConnectivity189` specializes this to the normalized #189 star.
   This deletion theorem does not drop an ambient low-degree exception.
2. **Cycle-to-terminal splice.** A cycle in A−x can be opened at two arbitrary
   distinct attachment vertices. Walk almost to the end of one arc, jump
   through x, and follow the other arc backwards to the target. This visits
   the entire cycle plus x. Hall supplies disjoint arms from arbitrary
   endpoints to the cycle in the root-deleted shore; a terminal already
   there needs a zero-length arm. The quantitative version gains an extra
   route vertex for each prescribed endpoint outside the cycle.
   `StarCycleClosure189` translates this into a contradiction when h≥11
   and the weighted count with that cycle length is large enough. The
   existence of a cycle of that length remains an explicit premise.
3. **Defect and gain accounting.** `FanDefect189` charges a loss of one for
   each endpoint in a bad set; `DefectRoutable189` allows such losses whenever
   there are equally many off-P cut ports. `FanGain189` dually credits a
   known endpoint gain twice. `HookMark189` shows that any marked shore
   vertex with a cut neighbor can be a hook root by an exchange, using the
   fact every exact cut port is already used by a full hook.
4. **Actual split branch closed.** `SplitRoutes189` builds alternating paths
   with loss exactly one per small-side endpoint. `OffPathBoundaryBudget189`
   bounds ambient degree by induced-shore degree, pin count and off-P cut
   ports. `StarSplitClosure189` then eliminates a minimum-height
   `h=k+1` normalized separated-double star whose two parts have sizes m
   and m+1, all cross edges, and the larger part independent. The smaller
   part's own edges are unrestricted. No theorem classifies every
   non-Hamilton-connected shore as such a split in this package.
5. `SeparatedRootReduction189` combines the preceding publication's
   Hamilton-connected branch elimination with root alternatives: d≥9 yields
   a replacement double of degree d or d+1, or a radius-three
   minimum-degree single. This does not assert root replacement terminates.

[Complete pinned Lean sources](proof-sources.tar.gz). Extract the archive and use its replay script.
