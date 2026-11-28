# Graffiti.pc #384b: all graphs with seven or eight triangle-count types

The bound is proved for every finite simple graph with exactly seven or eight distinct counts of triangles incident to a vertex, including disconnected graphs. There is no restriction on graph order. With either count, the bound is (\gamma_2(G) \le |V(G)|-4). See [the Lean theorem](src/PaletteSevenEight384b.lean). The general conjecture remains open.

1. At least six vertices have degree at least two. With ten or more such vertices, the earlier nonleaf bound already guarantees four omissions.
2. For a graph with six to nine nonleaves, induce on those vertices. Every positive triangle count is preserved. In the core, choose two vertices whose triangle counts are at least five. Both have degree at least four. Four common neighbors can be omitted directly.
3. Otherwise sort each other vertex by its two anchor adjacencies. The four core sizes have respectively 3, 8, 16, and 28 possible anchor shapes. For each shape a kernel-checked finite tree examines its free edges. A leaf either excludes the required palette of six positive counts or supplies four vertices to omit. The numerical checker is proved sound in [SmallPalette384b.lean](src/SmallPalette384b.lean); no solver is run at replay.
4. A checked omitted vertex either has two graph neighbors outside the omitted set, or has no neighbor inside it. In the latter case its original degree supplies both required neighbors, even if one or both were removed when forming the core. This avoids assuming the nonleaf core itself has minimum degree two.

## Reproduce

Use Lean 4.19.0 and Mathlib v4.19.0. Compile the [baseline](../graffiti-384b-partial) and [odd-quota prerequisites](../graffiti-384b-diversity29), including their transitive input modules. Add their object directories and Mathlib to LEAN_PATH and run `bash replay.sh`. The replay checks SHA-256 digests, compiles fresh package modules with warnings as errors, and prints standard-axiom reports. The normalized anchor and two-edge score correspondences adapt the earlier [eight-nonleaf package](../graffiti-384b-eight-nonleaves).
