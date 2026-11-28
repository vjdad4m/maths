# Graffiti.pc #384b. Original neighbors of the two cubic vertices

Let $J$ be the spanning subgraph of a finite simple graph $G$ retaining every edge that belongs to a triangle. The score of a vertex is the number of incident triangles in $G$. In the connected catalogue problem of order greater than two, assume that no vertex has score one.

**If a vertex of score zero is adjacent in $G$ to a vertex of degree three in $J$, the catalogue bound holds.** In particular this covers a leaf attached to either skeletal cubic. It imposes no order or diversity cutoff. [CubicLeaves.lean](CubicLeaves.lean)

In every hypothetical failure, all original neighbors of either skeletal cubic have degree at least three in $J$ and belong to the same connected component of $J$ as that cubic. An original edge at a cubic which is absent from $J$ crosses every maximum cut of $J$. [CubicLeaves.lean](CubicLeaves.lean) · [CubicComponent.lean](CubicComponent.lean)

A second all-order sufficient condition applies when one skeletal cubic has original degree at least four. Four distinct usable pivots then suffice for the catalogue inequality. A pivot is usable if two disjoint sets of original vertices, both avoiding the pivot, give every pin at least two neighbors in the other set and give the pivot at least two neighbors in **each** set. A square contained in the pivot's neighborhood is one such construction. All pin edges may be original edges, including edges absent from $J$. [OriginalPins.lean](OriginalPins.lean)

## Why a cubic cannot carry a leaf

The previous fixed-cubic theorem puts exactly two nonadjacent cubics at the two vertices having just two crossing neighbors in every maximum cut of $J$. Each has a unique same-shore skeletal neighbor. If it had a second original neighbor outside the opposite high shore, the previously verified exposure lemma would force it to be adjacent to a second critical vertex. This contradicts nonadjacency. Therefore its only original neighbor outside the opposite high shore is its unique same-shore skeletal neighbor. Every unsupported edge at this cubic must cross every maximum cut. Flipping the colors of a whole component preserves the cut value; an edge between components could then be made monochromatic. This also proves the component restriction.

For the second result maximize a pinned cut after removing the pivot's incident original edges. When a selected unpinned vertex has skeletal degree at least three, it can obstruct the shared omission only when it has degree three in both graphs, has exactly the same neighbors in both, and is adjacent to the pivot. The theorem `actual_blocker` states the general result for any set of selected vertices $W$ with $|T|\le |W|+1$ and every unpinned member high in $J$. When count one is absent, take the high set itself. If one of the two cubics has an extra original edge, the other cubic would have to cover all four pivots with just three neighbors.

## Included predecessor

The embedded wheel-cut source archive contains the order-independent octahedron and seven-center sufficient conditions, the forbidden even cycle through the score-three cubic in one of its neighbors' links, and the count-one ear-and-rim sufficient conditions. It includes the exact eleven-vertex test and an explicit thirteen-vertex example separating the private-triangle and even-cycle conclusions. Extract that inner archive to read its detailed README and the seven wheel modules. [Wheel-cut sources](graffiti-384b-wheel-cuts-sources.zip)

The earlier upper-palette and leaf-exposure proofs supply the fixed pair, the equivalence with absence of score one, the triangle-edge degree estimate, and the critical-neighbor conclusion used here. The region-flip proof uses the predecessor's exact finset color-flip definition. The pinned-cut argument reuses the wheel-stage weighted omission inequality.

These theorems leave the general odd-diversity, zero-realized case open for this project. No exhaustive search or numerical assumption is used in the new three modules.

## Replay and source manifest

The embedded 69-module source archive has SHA-256 `9c5d4c228db6400f74febc6835a3a720e12a555d8b53262db463c16ea6aeff24`. The three new modules add eight axiom reports. The complete chain contains 72 project modules. Set the two paths below to the Lean 4.19.0 binary directory and the built Mathlib v4.19.0 checkout, then run the entry point in the extracted source archive.

~~~sh
export CROSSFOUR_LEAN_BIN=/absolute/path/to/lean-4.19.0-linux/bin
export CROSSFOUR_MATHLIB=/absolute/path/to/built/mathlib4
python3 -B replay_original_pins.py
~~~

The default command compiles the nested dependency chain from source. A segmented replay can reuse a full wheel-stage cold log using `--wheel-log /absolute/path/to/CompleteCold.log`. It authenticates the 69 object hashes before compiling the three modules. The release includes that full 69-module cold log followed by the three-module continuation. Every reported axiom belongs to the standard list, and the replay checks exact source and object hashes, warnings as errors, and the forbidden-declaration scan. [Replay entry point](replay_original_pins.py) · [Source hashes](SOURCES.sha256) · [Object hashes](OBJECTS.sha256)

[Complete pinned Lean sources](proof-sources.zip). Extract the archive and use its replay script.
