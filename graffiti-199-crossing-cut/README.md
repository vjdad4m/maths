# Graffiti.pc #199 three-cuts and vertex smoothing

## Scope

All graphs are finite and simple. The minimum-order hypothesis is the existing Lean predicate SmallerAtThree. It says that every smaller graph with vertex connectivity at least three and induced-tree number at most five is traceable. The published lemma smallerAtThree_of_catalogue_minimum derives it from a minimum counterexample to the catalogue conjecture.

- **cutTorso_connectivity** and **cutTorso_treeNumber_le** justify completing a cut to a clique on the retained side. For the tree bound, the discarded side is connected and every cut vertex has a contact there. **traceable_both_cutTorsos_of_smaller** gives a spanning path on each completed side of a three-cut into two connected shores.
- **traceable_after_smoothing_of_smaller** yields a spanning path in the graph obtained by deleting any vertex and making its open neighborhood a clique. The ambient graph has order at least five, connectivity at least three, and induced-tree number at most five. **cubic_smoothing_remainder** shows that in a nontraceable graph, a cubic vertex has a smoothing path with either zero filled transitions or two consecutive filled transitions, using all three of its neighbors. Exactly one filled transition lets the omitted vertex be inserted.
- **traceable_of_two_vertex_shore_of_independent_cubics** rules out a two-vertex component after a three-cut in a minimum-order nontraceable graph with independent cubic vertices. The proof needs independent cubic vertices only to guarantee that one endpoint of the component edge sees all three cut vertices.
- **large_crossing_failure_of_independent_cubics** applies directly to the negation of CrossingBetweenSurvivingEdges. At a crossing failure the deletion consists of three vertices and has two distinct components of order at least three. **LargeCrossingFailure.cubic_port_profile** further restricts any cubic cut vertex. The two components exhaust the survivors. The cubic vertex has no neighbor in the cut and exactly one contact in the clique component. The other component is nonclique.
- **CrossingRawWitness** verifies a graph on eight vertices of connectivity exactly three and induced-tree number at most five with exactly one cubic vertex and a failed crossing law. A three-clique joins two disjoint edges and a singleton. The witness has a Hamiltonian path.

The crossing law remains unproved for arbitrary minimum nontraceable graphs. The remaining crossing failures with a cubic cut vertex have a clique side of order at least three and a connected nonclique side of order at least three. When the cut contains no cubic vertex, the checked reduction still gives two components of order at least three. The independent-cubic branch in which crossing holds and the unrestricted conjecture remain open.

## Proof

An induced tree in a clique-completed shore contains at most two cut vertices. A filled edge of that tree can be replaced by a shortest connector through the discarded side. Its internal vertices have no other neighbors in the tree, because the cut separates them from the retained interior. The rank proof checks the induced-tree lift. Connectivity follows by projecting discarded survivors to one retained cut vertex.

For a two-vertex shore, smooth the endpoint that does not have to be universal to the cut. The remaining endpoint sees all three cut vertices, so only those three can participate in filled transitions. Zero filled transitions allow insertion next to the retained endpoint. One filled transition allows insertion directly. With two, the three cut vertices occur consecutively and the retained endpoint is next to that triple at a path end. Reorder that segment and restore the second shore vertex.

Three components behind a cut containing a cubic vertex give one contact per component. If two components are nontrivial, two length-two branches and the third contact make an induced six-vertex tree. If there are two large components, the cubic vertex has a unique contact into at least one. Any nonclique structure on that side can grow a three-vertex induced tree around that contact. Joining it to a length-two branch through the other side again gives six vertices. A cubic vertex with a neighbor in the cut would have a single contact on both sides, forcing both sides to be cliques. A spanning splice then uses all three cut vertices.

The proof reuses the published definition and reachability equivalence of the [surviving-edge crossing law](https://github.com/vjdad4m/maths/blob/main/graffiti-199-four-block-integration/src/RemainingCut.lean), the exact [minimum-order interface](https://github.com/vjdad4m/maths/blob/main/graffiti-199-cubic-contraction/MinimumContraction.lean), and the [rooted-tree rank](https://github.com/vjdad4m/maths/blob/main/graffiti-199-cubic-contraction/RootedTreeRank.lean). The published cubic-edge omission result supplies the setting of the [independent-cubic branch](https://github.com/vjdad4m/maths/tree/main/graffiti-199-cubic-triangle), and the new reduction uses the branch hypothesis explicitly.

## Replay

Lean 4.19.0, commit 6caaee842e94, with Mathlib v4.19.0 revision c44e0c8ee63ca166450922a373c7409c5d26b00b. Replay rebuilds the 30 published dependencies and 15 new modules in order with warnings as errors. SourceManifest.tsv and PublishedSources.tsv record ordered imports and source SHA-256 hashes, and PublicBlobAudit.tsv records the verified dependency blob IDs.

~~~sh
bash graff199-k3-cut-torso-codex/replay.sh --from-source
~~~

The shared workspace uses its existing publication checkouts. To replay elsewhere, pass the path to a checkout of vjdad4m/maths after --from-source and set GRAFF199_MATHLIB to a built checkout of the pinned Mathlib revision. Set GRAFF199_LEAN_BIN if Lean 4.19.0 is outside PATH.
