# A connected eleven-vertex realization of the upper-profile constraints

On ten vertices the positive core is connected, has no five-clique, and has score list [3,9,7,5,8,2,4,6,14,11]. Every edge is supported by a triangle. Vertices 0 and 5 are its only cubics and they are nonadjacent. The maximum cuts are precisely {0,1,2,3,4} and its complement. On both cuts the two cubics are exactly the high vertices with two crossing neighbors. The 2-domination number is 3. The set {1,2,8} and its complement both 2-dominate, giving a covered cut of sizes 3 and 7.

Adjoin vertex 10 as a leaf adjacent only to vertex 0. The resulting graph has eleven distinct vertex counts and its only zero is the leaf. The triangle-edge graph is the ten-vertex core together with the isolate 10. Thus it has exactly ten high vertices, so its high count is one smaller than its triangle diversity. The 2-domination number of the eleven-vertex graph is 4 and its catalogue bound is 5. The graph shows that the fixed cubics, five-clique exclusion and balanced maximum cut can all occur together in a graph satisfying the catalogue bound strictly. Alternative cuts can have a larger omission shore.

The edge lists, adjacency symmetry, both score lists, cube degrees, five-clique exclusion, all maximum cuts, the 2-domination numbers and the unbalanced cut are formally verified. The graph was discovered by a targeted heuristic search on equal-sized shores, with the two prescribed cubic vertices and same-shore branching allowed only among their crossing neighbors. That search established no enumeration coverage. [Core proof](UpperExample.lean) · [Original graph](UpperLeafExample.lean)

## Replay

Set CROSSFOUR_LEAN_BIN to the Lean 4.19.0 binary directory, and CROSSFOUR_MATHLIB to the built Mathlib v4.19.0 checkout. From the extracted source archive run `python3 -B replay_example.py`. To reuse a complete cold leaf-stage replay, run `python3 -B replay_example.py --leaf-log /absolute/path/to/CompleteCold.log`. The latter checks all 53 predecessor object hashes before compiling both example modules and checking each target and object hash. The certificate embeds the exact leaf-stage source archive. [Source hashes](SOURCES.sha256) · [Object hashes](OBJECTS.sha256)

[Complete pinned Lean sources](proof-sources.zip). Extract the archive and use its replay script.
