Warning: truncated output (original token count: 1263)
Total output lines: 28

# Graffiti.pc 199 — surviving edges after a three-cut

Theorem `traceable_of_two_large_components` proves the following minimum-order reduction at every order at least five. Let a finite simple graph have vertex connectivity at least three and largest induced tree of order at most five. Assume every strictly smaller finite simple graph satisfying those same two bounds has a Hamiltonian path. If deletion of three vertices leaves two distinct components of at least three vertices each, the original graph has a Hamiltonian path. Additional surviving components are allowed. This theorem has no cubic-vertex hypothesis.

For a graph whose degree-three vertices are independent, `traceable_of_independent_cubic_crossing_failure` proves traceability whenever the surviving-edge crossing property fails. Equivalently, in a minimum-order nontraceable graph in that branch, deleting at most three vertices puts all surviving edges in a single component. Isolated surviving vertices are allowed. `catalogue_minimum_crossing` derives the same conclusion from minimality for the original Graffiti.pc conjecture, using the exact finite vertex-connectivity definition. The case where crossing holds and the full conjecture remain open in this package.

The four main theorem names have the prefix `Graffiti199Depleted.Catalogue.Incomplete.`. Their statements appear in `src/CrossingClosure.lean` and `src/CatalogueCrossing.lean`. `Incomplete` is the namespace originally chosen for cut vertices with incomplete adjacency to a shore.

## Proof

1. For two connected shores, call the cut vertices `r`, `a`, and `b`. If `r` misses a vertex on the opposite shore, there is a spanning path through the first shore together with `r`, starting at a shore vertex adjacent to `a`. The proof constructs the path from the components outside the neighborhood of `r` and handles zero, one, or two components with a unique contact. If `b` also misses a vertex on the first shore, the symmetric construction consumes `b` on the other side. Joining at `a` covers the graph. The proof also handles the case where the same port is the sole incomplete port on both sides.
2. A rooted four-vertex tree can be extended to six using either a two-edge tail on the opposite shore or two nonadjacent leaves there. The endpoint construction with these alternatives proves `ShoreCut.full_clique_shore`. For any two-component three-cut in a non…63 tokens truncated…e induced deletion is still three-connected. If the further deletion of at most two vertices leaves a twin, every remaining component attaches to it. If all clique vertices disappear, the outside of the original clique is connected. Deletion preserves the induced-tree upper bound. Minimum order gives a spanning path in the smaller graph, and the omitted twin can be inserted. This excludes the two-component case.
4. For each cut vertex and surviving component, a clique completely adjacent to that cut vertex costs one vertex in an induced tree grown from the cut vertex. Any other component can supply two vertices, as independent neighbors or a two-edge tail. In a minimum nontraceable graph both distinguished large components fail to be fully attached cliques. The six-tree exclusions force exactly three components, all cliques. Hall's theorem gives distinct contacts for the required two ports in each large clique. Traverse the third clique first, followed by a port, the first large clique, a second port, the second large clique, and the last port.
5. The frozen theorem `large_crossing_failure_of_independent_cubics` supplies the two large components from failure of crossing. This is the only step needing independence of the cubic vertices.

The archived splice interface can consume the crossing theorem directly. For a caller requiring edge-to-edge reachability after a small deletion, apply `Graffiti199Depleted.edgeReach_iff_crossing_between_surviving_edges.mpr` to `catalogue_minimum_crossing`. The four-block layout in earlier splicing results has separate hypotheses.

## Reuse and replay

`Manifest.tsv` gives the deterministic compilation order, SHA-256, and source provenance of each module. The package contains 107 Lean sources. Eighteen belong to this reduction, and 89 are byte-for-byte dependencies of the frozen opposite-complete package. Its manifest attributes 76 of these to public repository paths and 13 to the earlier private proof. These include the earlier private-component bound, rooted neighborhood structure, clique paths, Hall attachments, and the crossing-failure adapter. The order-eleven finite refutations are not needed. The proofs use no solver certificates.

Set `GRAFF199_MATHLIB` to a Mathlib v4.19.0 checkout with the standard compiled dependencies and `GRAFF199_LEAN_BIN` to the Lean 4.19.0 bin directory when it is not already on PATH. From this directory run

```sh
bash replay.sh
```

The script checks the Lean version and Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`, checks all source digests, and builds every project module in a new temporary directory with warnings as errors and asynchronous elaboration disabled. The four graph-level conclusions depend on exactly `propext`, `Classical.choice`, and `Quot.sound`. The transcript is in `StrictReplay.log`.


To audit a freshly captured transcript, run `bash replay.sh > StrictReplay.log 2>&1` and then `python3 audit.py`. The audit checks the proof sources, their compile order, and the four transitive axiom lists.

[Complete pinned Lean sources](proof-sources.tar.gz). Extract the archive and use its replay script.
