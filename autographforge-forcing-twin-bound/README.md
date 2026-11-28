# Reusable forcing lemmas for twin blocks

This package extracts the argument behind [AutoGraphForge 842](../autographforge-842/), [2535](../autographforge-2535/) and [676](../autographforge-676/) into reusable Lean theorems.

- **Fort lemma.** If every outside vertex adjacent to a set has more than k neighbors in the set, k-forcing cannot enter that set when it starts entirely uncolored.
- **Twin quota.** For a block of m vertices with identical open neighborhoods, every k-forcing set must seed at least max(m − k, 0) vertices of the block. These quotas add over disjoint blocks.
- **Exact two-forcing number for page blocks.** Take n pairs of hubs. Attach m private pages to both hubs of each pair, with no other edges incident to the pages. Allow any graph whatsoever on the hubs. If m ≥ 3, the two-forcing number is exactly **n(m − 2)**. Seed all but two pages per block. The first round colors every hub, and the second colors all remaining pages. The twin quotas prove optimality.

[TwinForcing.lean](TwinForcing.lean) works with the repository's existing simultaneous forcing rule. [PageBlocks.lean](PageBlocks.lean) proves the exact formula without any planarity, chordality, or connectivity assumption. It covers the forcing calculations for both the fan chains and the book chains. A parametric Havel–Hakimi residue calculation and graph-class certificates are still needed for a full formalization of the unbounded-gap argument.

## Replay

Use Lean 4.19.0 and built Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`.

```bash
MATHLIB_DIR=/absolute/path/to/mathlib4 bash autographforge-forcing-twin-bound/replay.sh
```

Replay builds from source with warnings as errors and checks only `propext`, `Classical.choice`, and `Quot.sound`.
