# Kelmans: complementary rank unions and controlled six-switches

These are partial results for the (P_3)-factor approach to Kelmans’s conjecture. **They do not resolve the conjecture.**

Starting with a cubic core and some marked edges, consider complementary rank choices (the old graph with a perfect matching removed). A marked edge is represented by its two edges through a new subdivision vertex. The retained-mark budget limits which perfect matchings can be used.

- [Exact rank-union cut criterion](src/RemoteRankUnion.lean): a union of all chosen rebuilds is disconnected exactly when a nonconstant original cut consists only of unmarked edges belonging to every allowed complementary matching. If the family is nonempty and the original graph has minimum degree at least two, neither shore is a singleton.
- [Exact six-switch criterion](src/RemoteSixSwitch.lean): if the alternating six-switch touches two old components in a 2+1 pattern, two individually bypassable removed edges suffice to keep the touched vertices in at most two new components. An explicit residual-port condition is equivalent to actually merging them.
- [Square rank transfer](src/RemoteSquareSingleSlot.lean) and [controlled six-switch extension](src/RemoteSquareThenSix.lean): square choices and one designated safe six-switch suffice for a full factor when their union is connected, the old rebuilt rank is 2-regular after deleting the fixed omitted slot, and the total order is divisible by three. These are sufficient hypotheses, not a general way to guarantee such switch families.
- [Mixed six-switch repair](src/RemoteSixMixed.lean): in a split six-switch, two spanning paths using a mixture of old and new gate edges can still join the three residual runs. If the omitted slot touches any of four specified exposed ports, the union factors on that region at the right total order, although no individual rank is needed to support all tiles.

## Representative exact examples

Both examples are genuine 24-vertex wide remote boards of legal cubic, cyclically four-edge-connected, 3-vertex-connected order-26 hosts. They test the strategy, not the conjecture.

- [Forced cut example](fixtures/SquareUnionLock.lean): exactly two rank choices preserve a prescribed omission. Their true union has components of sizes 5 and 19 and cannot factor. The underlying remote board does factor.
- [Six-switch orientation example](fixtures/SixOrientationLock.lean): exactly two choices preserve a prescribed omission, and differ by one alternating six-cycle. Individually their components have sizes (8+16) and (11+13), so neither factors. Their true union is connected and admits an explicit factor.

Earlier square-family convergence is from [the related package](../kelmans-square-convergence/). Its Hamiltonian specialization for disjoint squares and a matching is an instance of [Kotzig’s compatible Euler-tour theorem](https://dml.cz/bitstream/handle/10338.dmlcz/136066/MathSlov_18-1968-1_8.pdf).

## Replay

Use Lean `v4.19.0` and Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. From a project with the corresponding Mathlib cache:

```sh
lake env bash /path/to/kelmans-switch-unions/replay.sh
# Optional exact ambient-geometry examples:
MATHS_REPO_ROOT=/path/to/maths lake env bash /path/to/kelmans-switch-unions/replay.sh --fixtures
```

The first command builds the complete bundled generic cone from sources in `modules.txt` into a fresh directory. The optional command additionally builds the exact upstream fixture cone from the public sibling packages, as pinned and topologically sorted in `fixture-dependencies.tsv`. Both use warnings as errors and CPU-kernel checking. `sources.sha256` pins the bundled source bytes. The displayed theorem audits use only Lean’s standard axioms (propositional extensionality, classical choice, and quotient soundness), or none.
