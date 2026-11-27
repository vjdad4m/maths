# Graffiti.pc #199 arbitrary one-omission gaps

## Scope

The graph is finite and simple, its induced-tree number is at most five, and a path spans the graph minus one cubic vertex. The omitted vertex has three independent neighbors, at least one of which is cubic. A gap is the number of edges on that path between successive visits to the three neighbors.

- Graffiti199Depleted.WiderOmission.traceable_of_separated_gaps proves traceability whenever both gaps have at least three edges. Both gaps can have arbitrary length.
- Graffiti199Depleted.WiderOmission.traceable_of_short_long_gaps handles one gap of two edges and the other of at least four edges under the archived minimum-order, connectivity-at-least-three, and surviving-edge crossing hypotheses. Reversing the path handles the opposite order.
- Graffiti199Depleted.WiderOmission.traceable_of_independent_omission excludes the independent-neighborhood branch entirely under those archived hypotheses. NeighborOrder.lean derives the path order of the three neighbors.
- Graffiti199Depleted.ContractedEdge.minimum_cubic_edge_other_neighbors_adjacent applies the theorem to the endpoint omission furnished by the archived cubic-edge contraction. In a nontraceable graph under its hypotheses, the two neighbors of the selected endpoint other than its cubic mate are adjacent. This reduces this line of attack to the triangle case.

## Length-independent splice

An interior fragment between two labeled vertices is retained as a unit. The checked route specifies either a single anchor or a traversal of one entire designated fragment. Its anchor list is a permutation of the anchors and the omitted vertex, its fragment list is a permutation of all designated fragments, and the connections between units are genuine graph edges. The expansion lemma constructs the spanning path and checks that its endpoints match the original block, so the exterior path segments stay attached.

The two finite anchor classifications range over ten labeled vertices and never enumerate the vertices inside any fragment. The separated case keeps two fragments, and the short-long case keeps one. An actual chord across a retained fragment is allowed in the graph, while a certificate using the fragment still traverses all of its vertices. The induced-tree witnesses always use genuine edges on the anchors. In the short-long case, the two rows without a certified route contain the published true-twin charts, which are forbidden under the archived hypotheses.

The proof reuses the [published gap-seven package](https://github.com/vjdad4m/maths/tree/main/graffiti-199-cubic-gap-seven) for the smaller gap bound, the true-twin chart exclusions, and the finite clause infrastructure. The triangle branch and general Graffiti #199 remain open.

## Strict replay

Lean 4.19.0 and Mathlib revision c44e0c8ee63ca166450922a373c7409c5d26b00b. SourceManifest.tsv records the ordered new sources. PublishedSources.tsv and PublicBlobAudit.tsv give the ordered pinned project dependency closure and the matching GitHub main blob IDs. StrictReplay.log records the warnings-as-errors build and theorem axiom reports.

~~~sh
bash graff199-k3-arbitrary-gaps-codex/replay.sh --cached
~~~

To rebuild the public project dependencies from source, run the same script with --from-source and the path to a checkout of the public repository. Outside the shared workspace, set GRAFF199_MATHLIB and optionally GRAFF199_LEAN_BIN.

From the repository root, set `GRAFF199_MATHLIB` to the pinned, built Mathlib checkout and optionally `GRAFF199_LEAN_BIN` to the toolchain's bin directory. Then run:

~~~sh
bash graffiti-199-cubic-arbitrary-gaps/replay.sh --from-source "$PWD"
~~~
