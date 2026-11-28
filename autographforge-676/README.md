# AutoGraphForge 676: three bridged books

**Disproved in Lean.** The [pinned statement](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L676), generated ID `11a73ea9`, asserts that the two-forcing number is at most the Havel–Hakimi residue for every nontrivial chordal K₄-free graph.

Start with three copies of K₂,₅ and add the edge between the two hubs in each copy. The five other vertices are its pages. Join the copies in a chain by bridges using distinct hubs in the middle copy. The result is connected and has 21 vertices.

- **Two-forcing number 9.** Three initially uncolored pages in any one book cannot receive a first force: either hub sees all three. Thus each book needs at least three seeds. With three pages seeded per book, the first round colors the hubs and the second colors the remaining pages. This transfers the argument from [row 2535](../autographforge-2535/).
- **Residue 7.** The sorted degrees are four 7s, two 6s, and fifteen 2s. Seven Havel–Hakimi pivots leave fourteen 1s. Reducing these leaves seven 0s.
- **Chordal and K₄-free.** Remove the pages first. Each has two adjacent hubs as neighbors. The remaining six hubs form a path, so its vertices can be removed from one end in order. No clique inside a book contains two pages, and any clique meeting two books is confined to the ends of one bridge. Lean checks the elimination order and absence of a four-clique.

[Witness676.lean](Witness676.lean) computes the two invariants and proves connectivity. [Chordal676.lean](Chordal676.lean) uses the [existing elimination theorem](../autographforge-book-forts/ChordalBasis.lean) and proves the literal negated catalogue statement, since 9 > 7.

The pinned release marks this exact entry proposed, without a recorded Lean proof. No matching ID was found in the inspected refutations and released Lean sources. The graph classes are the same as in the pinned [GraphCalc implementation](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/core/basics.py).

## Replay

Use Lean 4.19.0 and built Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`.

```bash
MATHLIB_DIR=/absolute/path/to/mathlib4 bash autographforge-676/replay.sh
```

Replay compiles from source with warnings as errors and verifies only `propext`, `Classical.choice`, and `Quot.sound`.
