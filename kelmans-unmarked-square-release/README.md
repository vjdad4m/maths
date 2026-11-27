# Kelmans: releasing two spokes of an unmarked square

Suppose a globally minimum-cost perfect matching of cost at most one uses all four exterior spokes of an induced square. Cost counts how many of six marked edges the matching uses. If the square is unmarked and the graph outside the square has no disjoint paths joining the two pairs of opposite exterior contacts, then a matching of cost at most one can release exactly two spokes, provided there is an explicit finite distribution of perfect matchings with edge marginals 1/3. Releasing a spoke means removing it from the matching, so its edge is restored in the complementary graph. The theorem's exact marking hypothesis excludes the chosen first endpoint of each mark from the square, so absence of every marked endpoint is sufficient.

[Main Lean theorem](src/RemoteSquareBudgetTheorem.lean). The proof derives the outside strips and weighted budget estimate. The second theorem derives the required distribution from an explicit partition into three perfect matchings; the existence of such a distribution for general cubic graphs is not formalized here. The result is local: it does not assert a single bounded-length exchange, a connected complementary graph, or a solution of Kelmans's conjecture.

- [Two-row ladder lemma](src/RemoteLadderNoDiagonal.lean): a walk using a vertical ladder edge cannot be disjoint from a walk crossing the full length. This is a reusable graph lemma, not a formal identification of a particular prism exterior with the ladder.
- [Diagonal example](fixtures/DiagonalReleaseFixture.lean): an exact legal 24-vertex remote board has a width-four square whose exterior joins opposite contacts. Releasing exactly two spokes has minimum cost two, although an explicit twelve-edge exchange releases all four at cost zero. The unrestricted board has a full P₃-factor.
- Related packages: [single-component budget exchange](../kelmans-budget-component/), [rank unions and controlled switches](../kelmans-switch-unions/), and [the minimum-budget eight-edge example](../kelmans-min-one-eight/).

## Replay

Use Lean 4.19.0 and Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. In a project with the corresponding Mathlib cache:

```sh
MATHS_REPO_ROOT=/path/to/maths lake env bash /path/to/maths/kelmans-unmarked-square-release/replay.sh
# Optional exact diagonal fixture:
MATHS_REPO_ROOT=/path/to/maths lake env bash /path/to/maths/kelmans-unmarked-square-release/replay.sh --fixtures
```

The script checks the bundled source SHA-256 manifest and verifies each upstream source against its pinned Git blob before rebuilding in a temporary directory with warnings as errors. [StrictReplay.log](StrictReplay.log) checks the complete generic source cone. [LocalFixtureReplay.log](LocalFixtureReplay.log) checks the exact optional fixture against previously verified local dependencies, including a thin `Handle189` overlay that differs from the public source only in its imports. The full optional public dependency manifest is provided but was not rebuilt for that log. Audited declarations use only Lean's standard axioms.
