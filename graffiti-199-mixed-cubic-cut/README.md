# Graffiti.pc #199 mixed cut at a cubic vertex

## Checked scope

The new result applies to a finite simple graph of connectivity at least three and induced-tree number at most five. It assumes independent cubic vertices and the two-component cut profile from the preceding crossing reduction. The cubic cut vertex has its unique neighbor in the clique component, two neighbors in the connected nonclique component, and zero neighbors in the cut. **CubicMixedCut.traceable_of_independent_cubics** constructs a Hamiltonian path under this profile.

In a minimum-order nontraceable graph with independent cubic vertices, **edge_reach_of_cut_with_cubic** proves that every two surviving edges are in the same component after any deletion of at most three vertices containing a cubic vertex. The theorem uses the published SmallerAtThree hypothesis and order at least five. **high_cut_of_crossing_failure_of_independent_cubics** reduces any remaining crossing failure to a three-vertex cut whose vertices all have degree at least four and whose deletion has two different components of order at least three. This leaves the high-degree-only cut case and the unrestricted conjecture open.

The preceding eight-vertex witness is a traceable graph defeating the raw crossing implication. Its offending separator consists of three high-degree vertices, and the unique cubic vertex survives that deletion. It lies outside the cubic-cut branch closed here.

## Construction

Let r be the cubic cut vertex, a its unique clique neighbor, and b and c its neighbors in the nonclique shore. A second clique vertex gives an induced two-edge tail at r. This forbids a four-vertex induced tree rooted at r on the nonclique side, since gluing that tree to the tail gives six vertices.

- If b and c are nonadjacent, the nonclique side is complete except for their missing edge. When the interior is small, the degree-four bounds at b and c ensure that the other two cut vertices can attach at distinct vertices while reserving an interior vertex for the missing transition.
- If b and c are adjacent, the vertices that see just one of b and c form two clique blocks with b and c respectively. The edge bc is the only edge between those blocks. The common neighbors in the interior form a clique universal to the shore. With zero common neighbors, a path uses bc and the two cut contacts. With one common neighbor, some cut vertex meets an exclusive block, and a pair of distinct contacts can include that vertex. With at least two common neighbors, every pair of distinct endpoints works.

Two distinct contacts let the clique shore be traversed from r to one other cut vertex. The constructed nonclique-shore path then leads to the remaining cut vertex.

The proof reuses the exact [minimum-order interface](https://github.com/vjdad4m/maths/blob/main/graffiti-199-cubic-contraction/MinimumContraction.lean), the [surviving-edge crossing law](https://github.com/vjdad4m/maths/blob/main/graffiti-199-four-block-integration/src/RemainingCut.lean), and the strictly replayed cut profiles in the [preceding cut-torso package](../graffiti-199-crossing-cut/). The public [cubic-edge omission closure](https://github.com/vjdad4m/maths/tree/main/graffiti-199-cubic-triangle) provides the context for the independent-cubic branch.

## Replay

Lean 4.19.0, commit 6caaee842e94, and Mathlib v4.19.0 revision c44e0c8ee63ca166450922a373c7409c5d26b00b. Replay checks all 30 published dependencies, the 14 needed frozen cut modules, and the 11 new modules in source order with warnings as errors. The top-level results report exactly propext, Classical.choice, and Quot.sound.

~~~sh
bash graffiti-199-mixed-cubic-cut/replay.sh --from-source /path/to/maths
~~~

Outside the shared workspace, set GRAFF199_MATHLIB to the built pinned Mathlib checkout and GRAFF199_LEAN_BIN if required. Pass the path to a checkout of vjdad4m/maths and the path to the preceding cut package after --from-source. PublishedSources.tsv, FrozenCutSources.tsv, and SourceManifest.tsv record the exact ordered source closures and hashes. PublicBlobAudit.tsv records the public dependency blob IDs.
