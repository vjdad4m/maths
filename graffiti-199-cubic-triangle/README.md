# Graffiti.pc #199 cubic-edge omission with a triangle

## Checked statements

- **Graffiti199Depleted.WiderOmission.traceable_of_triangle_omission**. Let a finite simple graph have vertex connectivity at least three and induced-tree number at most five. Suppose a path spans the deletion of a degree-three vertex z adjacent to a degree-three vertex w. If the other two neighbors of z are adjacent, the graph has a Hamiltonian path. This holds for arbitrary graph order and arbitrary gap lengths along the omission path.
- **Graffiti199Depleted.ContractedEdge.traceable_of_minimum_cubic_edge**. An edge joining two degree-three vertices forces traceability if the graph has connectivity at least three, induced-tree number at most five, and order at least ten, and satisfies SmallerAtThree and CrossingBetweenSurvivingEdges. SmallerAtThree says that all lower-order graphs with connectivity at least three and induced-tree number at most five are traceable. The crossing property requires an edge across any partition whose two shores each retain an edge after deleting at most three vertices.
- **Graffiti199Depleted.cubic_vertices_independent_of_minimum**. The degree-three vertices of a nontraceable graph with those same hypotheses form an independent set. This completes the archived cubic-edge branch. Graffiti.pc #199 remains open in general. The residual branch under the same reduction has independent degree-three vertices.

## Proof

The three neighbors of the omitted vertex occur in order on the path. If two are consecutive, insert the omitted vertex between them. A path endpoint adjacent to the omitted vertex also gives an immediate extension. Otherwise mark each neighbor and its predecessor and successor. The two gaps are either both at least three edges, exactly one is two edges (reverse the path if necessary), or both are two edges. The longest marked configuration has ten vertices including the omitted vertex.

A route can traverse an entire intervening path segment in either direction. The Lean certificate checks that the route visits each marked vertex and uses every segment once. Connections between segments must be real graph edges, and induced-tree witnesses use only real edges and nonedges. The separated classifier checks the needed route edges on partial adjacency assignments, so most assignments need not be expanded into individual rows.

For the configurations with no splice on the marked vertices alone, Lean checks the possible attachments of one, two, or three exterior vertices. A pair may already yield a splice or an induced six-vertex tree. In the remaining pairs, scanning one step closer to the endpoint either yields a splice or forces the same left attachment mask and the same adjacency to the right vertex. This propagation would make the endpoint adjacent to a forbidden successor of a neighbor of z. Two short configurations instead force a cut vertex. Every exterior vertex that can be reached from their leftmost marked vertex without going through its single marked neighbor has the same two marked contacts. Any edge leaving that part would give an induced six-vertex tree. Both arguments apply to interior and exterior segments of arbitrary length.

The proof reuses the segment expansion and ordered-neighbor lemmas from the [arbitrary-gap package](https://github.com/vjdad4m/maths/tree/main/graffiti-199-cubic-arbitrary-gaps). The exact contraction reduction from that package is what supplies the triangle hypothesis for the second theorem. The earlier true-twin charts are used in the published independent-neighborhood elimination invoked by that reduction. In the triangle case the adjacency on the two nonmate neighbors changes the charts. The new exterior certificates use the attachment-profile transfer from the earlier flank proof and check the changed charts directly.

## Replay and provenance

Lean 4.19.0, commit 6caaee842e94, with Mathlib v4.19.0 revision c44e0c8ee63ca166450922a373c7409c5d26b00b. Replay sets warnings as errors. The three top-level declarations report exactly propext, Classical.choice, and Quot.sound. The finite certificates use Lean kernel reduction.

~~~sh
bash graffiti-199-cubic-triangle/replay.sh --from-source "$PWD"
~~~

From the repository root, set GRAFF199_MATHLIB to a checkout of the pinned Mathlib revision with its Mathlib and dependency builds, and set GRAFF199_LEAN_BIN to the directory containing the pinned Lean if it is outside PATH. Both modes verify source SHA-256 hashes. The cached replay passed and rebuilt all 46 new modules in a fresh directory using 103 hash-checked public dependencies. See StrictReplay.log. The source-only attempt stopped with exit 137 while compiling the published Rows25.lean dependency. See SourceOnlyAttempt.log. SourceManifest.tsv contains the ordered new source files and their direct imports. PublishedSources.tsv supplies the ordered transitive closure of public project modules. PublicBlobAudit.tsv maps those files to the GitHub blob IDs.
