# Exact forcing and Havel–Hakimi residue for hub–page chains

This package connects the [Havel–Hakimi degree-list calculations](../autographforge-residue-phases/) to the [hub–page construction and its exact two-forcing number](../autographforge-forcing-twin-bound/).

Each block consists of two hubs and m independent pages, each adjacent to both hubs. Join the right hub of each block to the left hub of the next. In a book chain the two hubs in each block are adjacent; in a fan chain they are not.

Lean verifies the exact degree multiset for these explicit chains and the following formulas with j+3 blocks and 4j+9 pages per block:

| Chain | Two-forcing number minus Havel–Hakimi residue |
|---|---:|
| Fan | 2j² + 8j + 7 |
| Book | 2j² + 7j + 4 |

Both chains are connected. The fan chain has a proper two-coloring: color the hubs by block parity, and give the pages the opposite color. Lean also constructs a uniform planar drawing: the two hubs of block i are at (3i, 0) and (3i+2, 0), and page p is at (3i+1, p+1). Every open edge segment occupies a unit-width interval between integer columns. Inside one such interval the horizontal coordinate fixes the interpolation parameter, and the vertical coordinate then distinguishes edges. The theorem **`TwinForcing.fan_gap_unbounded`** in [FanPlanar.lean](FanPlanar.lean) proves that two-forcing minus residue is unbounded even on connected planar bipartite graphs. This strengthens the finite [#842](../autographforge-842/) and [#2535](../autographforge-2535/) counterexamples.

The book chain is chordal and K₄-free. In the elimination order, each page has at most two remaining neighbors and they are adjacent. After removing the pages, the hubs form a path, so each hub has at most one remaining neighbor. This yields the fully checked theorem **`TwinForcing.book_gap_unbounded`** in [BookClasses.lean](BookClasses.lean): for every natural number M there is a connected chordal K₄-free graph whose two-forcing number exceeds its residue by more than M. This strengthens the finite [AutoGraphForge #676 counterexample](../autographforge-676/).

**Replay:** use Lean 4.19.0 and a built Mathlib checkout at `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Run `MATHLIB_DIR=/path/to/mathlib bash replay.sh`. The script builds all dependencies into a fresh temporary directory and audits the named theorems' axioms.
