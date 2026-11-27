# Kelmans: two specified cheap complementary ranks can fail even together

This is an obstruction to a restricted proof strategy, not a counterexample to Kelmans's conjecture or to Remote T2. In this example the original 54-vertex board has a P₃-factor, and a separate budget-feasible rank also has one.

- **Ambient geometry.** The 48-vertex simple cubic cyclic-four core has six independent marked edges. The checked remote-board handle construction gives a 56-vertex simple cubic 3-connected cyclically four-edge-connected host. Delete its two adjacent poles and the specified remote edge. Its survivor is exactly the six-slot 54-vertex expansion.
- **The tested pair.** Two cost-zero complementary matchings differ on one alternating 36-cycle. Relative to the unmarked square on {1,2,7,8}, the first matches its four spokes and the second releases all four. Both diagonal cyclic orders give the same phase for ports {0,9,18,27}; the short ears have one and two internal vertices. The exact rebuilt-rank union includes all five divisible ears; they have not been discarded in the obstruction.
- **Why the union fails.** Outside the four ports there are six disjoint sealed groups whose orders are 14, 11, 11, 11, 2 and 1. Every P₃ tile disjoint from the four ports is entirely inside one group, so at least the group's order modulo three must be covered by tiles that use a port. These demands sum to 11. At most four port-touching tiles can use the four ports, and each contains at most two non-port vertices. Capacity is at most eight. Thus the exact union has no P₃-factor, and therefore neither of its two ranks does.
- **Positive scope check.** The full physical board has the explicit factor in the separate Ambient module. A third cost-zero rank with an independent factor is certified by ThirdRank. This prevents mistaking a bad pair for a failure of all rank choices.

The generic port-capacity result holds for any finite simple graph and arbitrary finite families of disjoint pieces closed outside the port set; pieces need not be connected or exhaustive. It is a necessary condition, not sufficient.

## Replay

Use Lean 4.19.0 and Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. In a project with that Mathlib cache:

```sh
MATHS_REPO_ROOT=/path/to/maths lake env bash /path/to/maths/kelmans-genuine-mixed54/replay.sh
MATHS_REPO_ROOT=/path/to/maths lake env bash /path/to/maths/kelmans-genuine-mixed54/replay.sh --fixtures
```

The script verifies the bundled source hashes and pins each upstream source by Git blob. [StrictReplay.log](StrictReplay.log) checks the generic source cone. [LocalFixtureReplay.log](LocalFixtureReplay.log) checks the exact fixture sources as separate modules using the verified local dependency objects, including a thin `Handle189` overlay whose source differs from the public module only in imports. The optional full public upstream cone was not rebuilt for that log. The structural host proof uses 22 verified handle operations rather than exhaustive 48-vertex cut enumeration. The axiom audits show only Lean's standard axioms.
