# Kelmans: a genuine diagonal phase obstruction and a square-side repair

This package studies one limitation of a path-based repair strategy. It does not disprove Kelmans's conjecture.

- [Genuine remote board](fixtures/DiagonalPhaseHost.lean): the board has 30 vertices and comes from a cubic, 3-vertex-connected, cyclically four-edge-connected host of order 32. [The two displayed cost-zero matching ranks](fixtures/DiagonalPhaseRanks.lean) each lack a P₃-factor. Their exact pairwise rebuilt union has an explicit P₃-factor. The [diagonal base](fixtures/DiagonalPhaseFixture.lean) has two cyclic orders; in either order the literal ears with one and two interior vertices attach at ports with both open gaps equal to 2 modulo three. The other two ears have divisible interior lengths.
- [Bare two-ear subgraph and repair](fixtures/DiagonalPhaseBare.lean): for either cyclic order, the bare 15-vertex subgraph cannot factor. Adding either one of the two omitted square sides individually restores a full factor on those same vertices. All these subgraphs embed into the genuine pairwise union; there is no claim that the bare subgraph is induced or that the whole union fails.
- [Generic extra-edge lemma](src/RemotePhaseChordRepair.lean): for two disjoint residual paths with the specified divisible runs, one extra edge from a suitable split vertex to the endpoint of the other path repairs their combined support. This is a sufficient path-shape condition, not a general repair theorem.

Related: [mixed diagonal paths and the abstract two-ear model](../kelmans-mixed-diagonal/), and [unmarked square release](../kelmans-unmarked-square-release/).

## Replay

Use Lean 4.19.0 and Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. In a project with that Mathlib cache:

```sh
MATHS_REPO_ROOT=/path/to/maths lake env bash /path/to/maths/kelmans-diagonal-phase/replay.sh
MATHS_REPO_ROOT=/path/to/maths lake env bash /path/to/maths/kelmans-diagonal-phase/replay.sh --fixtures
```

The script verifies SHA-256 digests of bundled sources and pins upstream sources by Git blob before rebuilding with warnings as errors in a temporary location. [StrictReplay.log](StrictReplay.log) checks the generic source cone. [LocalFixtureReplay.log](LocalFixtureReplay.log) checks the exact fixtures against previously verified local geometry dependencies, including a thin `Handle189` overlay whose source differs from the public module only in imports. The full optional public dependency manifest is provided, but was not rebuilt for that log. The audits use only Lean's standard axioms.
