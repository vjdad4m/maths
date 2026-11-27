# Kelmans: budget-feasible rank edges from one exchange

Let `p` be a perfect matching minimizing the number of marked edges it uses. If another matching `q` leaves a particular edge of `p` exposed in the complementary rank, one can expose that edge by exchanging just its alternating component of (pcup q). The exchanged matching uses at most as many marked edges as `q`. The proof compares the splice with its reciprocal splice and uses global minimality of `p`.

Consequently, at any budget admitting `p`, the union of admissible complementary rank edges equals the union from `p` and its budget-feasible single exchanges. See [the Lean proof](src/RemoteBudgetComponent.lean). This is an edgewise statement: it does not guarantee a common rank realizing all the edges, connectivity of the union, or a resolution of Kelmans's conjecture.

## Replay

Use Lean 4.19.0 and Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. With the Mathlib cache available, run:

```sh
MATHS_REPO_ROOT=/path/to/maths lake env bash /path/to/kelmans-budget-component/replay.sh
```

The script verifies all pinned source digests, rebuilds two modules from the [switch-union package](../kelmans-switch-unions/), and then checks this proof with warnings as errors. [StrictReplay.log](StrictReplay.log) records an independent rebuild of this complete source cone with the pinned Mathlib cache. The audited declarations use only Lean's standard axioms.
