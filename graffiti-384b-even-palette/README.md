# Graffiti.pc #384b for every even triangle-count diversity

Let G be a finite simple graph on n vertices. Write T for the set of distinct vertex triangle counts, including zero if realized. A two-dominating set D gives every vertex outside D at least two distinct neighbors in D. Let γ₂(G) denote the minimum size of such a set.

**If |T| is even, then γ₂(G) ≤ n − |T|/2.** This includes every order and every even diversity, in particular 12, 14, 16, 18, 20, 22, 24 and 26. The proof allows disconnected graphs.

The stronger theorem is **2γ₂(G) + |T ∖ {0}| ≤ 2n**. Equivalently, at least half the number of positive triangle-count types, rounded up, can be omitted from a two-dominating set. The catalogue bound therefore also holds whenever zero is absent, for either parity. Every counterexample to #384b must realize zero and have odd diversity. If it has 2k+1 types, including zero, the positive-type bound gives k omissions and the catalogue asks for k+1. [Theorems and set existence](PositivePalette384b.lean)

## Proof

Delete every edge that belongs to no triangle, retaining all vertices. This spanning graph J preserves every vertex triangle count and every two-dominating set in J works in G. Call a vertex of J *high* if its degree is at least three. Every triangle-count type at least two is realized by a high vertex. Every positive count realized outside the high vertices equals one, and each of these vertices has degree two and lies on a triangle. [Reduction to triangle edges](PositivePalette384b.lean)

We seek a cut such that each high vertex has two neighbors across it. A maximum cut already achieves this, since each vertex has at least as many neighbors across the cut as on its own side. If the positive types need one more representative, choose a single degree-two vertex e of count one. We can require two crossing neighbors for e as well, allowing all other degree-two vertices to be colored freely. Let a and b be the neighbors of e. Open the triangle eab by removing its three edges.

* **There is a path between a and b in the opened graph.** A simple such path has length at least two and avoids e. For odd length, the first edge of the path lies on a triangle with a third vertex z distinct from e. If z is off the path, insert it to change parity. If z is on the path, take the suffix starting at z and choose the one-edge or two-edge prefix from a to z that makes its total length even. Closing the even path through e gives an even cycle. Pin its colors alternately and maximize the cut over the remaining vertices. Every pinned vertex gets two crossing cycle neighbors and every unpinned high vertex gets at least two crossing neighbors. [Even cycle and parity detour](PaletteEvenCycle.lean)
* **The two anchors are in different components of the opened graph.** Maximize a cut there, then orient the components so that a and b are on the same side and put e on the opposite side. Restoring the triangle gives e two crossing neighbors. Each high anchor has at least one neighbor left after the triangle was opened, hence at least one crossing neighbor there, and gains e as a second. All other high vertices retain their original crossing neighbors. [Separated-anchor construction](PaletteEarSeparation.lean)

Let W consist of the high vertices and, when needed, the chosen e. Its triangle-count image covers all positive types. The larger of the two intersections of W with the cut sides contains at least ⌈|W|/2⌉ vertices. Omit that intersection. Every omitted vertex keeps its two crossing neighbors, which proves the claimed inequality. [Counting and pinned-cut completion](PartialPaletteCut.lean)

## What was reused

The public one-ear proofs use a singleton hypothesis on the entire degree-two set. This extension protects only the vertices in W. It reuses the published pinned-cut existence theorem, the indexed route and its suffix/prepend operations, the path extraction lemma, the triangle-edge count-preservation lemma, and monotonicity of γ₂ under adding edges. The two route cases have new conclusions about crossing neighbors for W. The earlier even lift with fewer nonleaves and the rank sampler for exactly 28 types are compatible with the result. The new proof covers all nonleaf counts without either hypothesis or any numerical rank table. [Public problem index](https://github.com/vjdad4m/maths/blob/b33aad93ffcaab8f8c9e21a6fc56592675782f6f/README.md) · [Earlier singleton-ear theorem](https://github.com/vjdad4m/maths/blob/b33aad93ffcaab8f8c9e21a6fc56592675782f6f/graffiti-384b-one-ear/src/OneEarFinish384b.lean) · [Earlier parity detour](https://github.com/vjdad4m/maths/blob/b33aad93ffcaab8f8c9e21a6fc56592675782f6f/graffiti-384b-one-ear/src/OneEarRoute384b.lean) · [Even-diversity lift](https://github.com/vjdad4m/maths/blob/b33aad93ffcaab8f8c9e21a6fc56592675782f6f/graffiti-384b-diversity30/EvenNonleaves384b.lean)

## Source and verification

Four top-level Lean modules form the new proof. A fifth, [PalettePrerequisites.lean](PalettePrerequisites.lean), imports four individual proof declarations from the frozen corpus by copying their proof bodies. This reduces the transitive import closure from 155 predecessor modules to 19. [Declaration provenance and hashes](SOURCE-MAP.tsv) records the source text before the visibility and namespace changes. The archive includes those 19 predecessor modules under `prior/`. Each predecessor source and the associated checked object were authenticated against the frozen diversity-28 source archive, SHA-256 `d9be366dedc310f2f283118bcbceb3b0fbd07ff33f37558248696622ad5cd400`. [New sources](NEW-SOURCES.sha256) · [New objects](NEW-OBJECTS.sha256) · [Predecessor sources](PRIOR-SOURCES.sha256) · [Checked object map](CHECKED-OBJECTS.tsv)

The replay entry point requires Lean 4.19.0 at `6caaee842e94` and the built Mathlib v4.19.0 at `c44e0c8ee63ca166450922a373c7409c5d26b00b`. It runs with warnings as errors and checks the axiom reports against `propext`, `Classical.choice` and `Quot.sound`. No external graph enumeration or solver certificate enters the proof. From the extracted sources, set the following to the local toolchain paths and run the cold replay to recompile all 24 project modules. The alternative checked mode authenticates the 19 predecessor objects first and rebuilds the five top-level modules. Both modes verify the hashes of the resulting new objects. [Replay entry point](replay.py)

~~~sh
export CROSSFOUR_LEAN_BIN=/absolute/path/to/lean-4.19.0-linux/bin
export CROSSFOUR_MATHLIB=/absolute/path/to/mathlib4
python3 -B replay.py --cold
~~~

~~~sh
python3 -B replay.py --checked /absolute/path/to/shared/workspace
~~~

[Complete pinned Lean sources](proof-sources.zip). Extract the archive and use its replay script.
