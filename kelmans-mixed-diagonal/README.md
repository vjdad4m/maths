# Kelmans: mixed diagonal paths and ear attachment

These are partial results for the P₃-factor approach to Kelmans's conjecture, not a resolution.

- [Mixed diagonal construction](src/RemoteFourUnionWeave.lean): two disjoint opposite paths are expanded by inserting their marked-edge slots. With the four unmarked square sides this gives two cyclic orders in the actual union of two rebuilt ranks. If one entire attached ear can be joined to that cycle, the combined order is divisible by three, and all remaining vertices split into disjoint divisible paths, the theorem gives a full P₃-factor in both the mixed union and the original expanded board. It does not assert that every cheap four-spoke release provides these paths and ears.
- [One-ear cycle lemma](src/RemoteFourMixedCycle.lean) and [two-ear residue criterion](src/RemoteDiagonalEarPhases.lean): the first opens a cyclic order at the attachment point and joins a whole ear. In the second, ears of orders 1 and 2 modulo three can be distributed over disjoint open arcs when the total order is divisible by three and the two gap orders are not both 2 modulo three.

## Exact examples and their different scopes

- [Genuine diagonal board, two fixed ranks](fixtures/DiagonalPairUnion.lean): the two selected cost-zero ranks each lack a factor, with closed parts of orders 4 and 10 respectively. Their exact pairwise union is connected and contains an explicit P₃-factor. This concerns those two ranks, not a claim about all budget-feasible ranks. The ambient geometry is supplied by the pinned [diagonal fixture](../kelmans-unmarked-square-release/fixtures/DiagonalReleaseFixture.lean).
- [Abstract two-ear model](models/RemoteMixedDissociation.lean): a 21-vertex graph with two ears has a 15-vertex set meeting each P₃ in at most two vertices, so a seven-tile factor is impossible. This is not a genuine remote survivor of a cubic host in the Kelmans reduction and is not asserted to come from an actual six-mark budget exchange. It limits the unrestricted two-ear construction, not Kelmans's conjecture.

Related: [rank unions](../kelmans-switch-unions/), [single-component budget exchanges](../kelmans-budget-component/), and [opened cycle chains](../kelmans-prism-ladder/).

## Replay

Use Lean 4.19.0 and Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. In a project with that Mathlib cache:

```sh
MATHS_REPO_ROOT=/path/to/maths lake env bash /path/to/maths/kelmans-mixed-diagonal/replay.sh
MATHS_REPO_ROOT=/path/to/maths lake env bash /path/to/maths/kelmans-mixed-diagonal/replay.sh --fixtures
```

The script verifies SHA-256 digests for bundled sources, pins upstream modules by Git blob, and builds with warnings as errors in a temporary directory. [StrictReplay.log](StrictReplay.log) checks the generic modules and the abstract model from sources. [LocalFixtureReplay.log](LocalFixtureReplay.log) checks the exact genuine fixture supplement against previously verified local dependencies, including a thin `Handle189` overlay whose source differs from the public module only in imports. The full optional public dependency manifest is provided, but was not rebuilt for that log. Audited declarations use only standard Lean axioms, or none.
