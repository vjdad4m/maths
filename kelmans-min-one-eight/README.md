# Kelmans: an eight-edge neutral exchange at minimum budget

This is a finite test of a complementary rank repair strategy, not a counterexample to Kelmans's conjecture.

The construction has an 18-vertex cubic core and six marked edges. Every perfect matching uses at least one marked edge. Two explicit matchings `Q₀` and `Q₁` both use only the marked edge 9–10, so both attain the true minimum budget of one. A single alternating eight-edge exchange takes `Q₀` to `Q₁`, restoring two edges of a four-edge cut. The rebuilt rank at `Q₀` has components of orders 6 and 18. The rebuilt rank at `Q₁` is connected and admits an explicit full P₃-factor. The 24-vertex board is the verified wide remote survivor of a cubic, cyclically four-edge-connected, 3-vertex-connected 26-vertex host.

- [Exact minimum and eight-edge repair](src/MinOneEight.lean)
- [Exclusion of a shorter neutral single exchange from this start](src/MinOneEightShorter.lean): every genuine alternating square or six-cycle changes the marked-edge count. This does not exclude moves that leave the minimum budget, and does not say the disconnected starting rank lacks a factor.

## Replay

Use Lean 4.19.0 and Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. With the Mathlib cache available, run:

```sh
MATHS_REPO_ROOT=/path/to/maths lake env bash /path/to/kelmans-min-one-eight/replay.sh
```

The script pins the complete public fixture dependency order inherited from [the switch-union package](../kelmans-switch-unions/) and rebuilds it in a fresh directory before checking the two local modules. The [local replay log](LocalFixtureReplay.log) records an independent build of the two exact fixture sources against the previously verified dependency objects, using a thin `Handle189` overlay whose source differs from the public module only in imports. That local replay did not rebuild the full public dependency manifest. The audited declarations use only Lean's standard axioms.
