# graffiti-199-order-eleven-closure

For finite simple graphs on eleven vertices with connectivity at least three, largest induced tree of order at most five, and independent degree-three vertices, a three-cut with connected shores of sizes 3+5 or 4+4 implies traceability. The theorem for each explicit cut and the combined minimum-order crossing-failure theorem are audited in CombinedOrderEleven.lean. The latter branch now needs at least twelve vertices, given the earlier lower-order premise and order at least five. The general catalogue question remains open.

All graph-to-label bridges and reverse unit propagation steps are Lean source. The compressed 4+4 terminal module Fused44.lean includes the graph-level wrapper. No external SAT solver is needed for replay. The 3+5 refutation ends at clause 5026 and the 4+4 refutation at clause 3754.

## Verification

In a shell with Lean 4.19.0 available, set GRAFF199_MATHLIB to the Mathlib v4.19.0 checkout with its standard compiled library. GRAFF199_LEAN_BIN may point to the toolchain bin directory. Run from this package directory.

```sh
bash replay.sh
```

The script checks the pinned versions, validates every listed SHA-256, compiles all sources in dependency order with warnings as errors, and prints the final theorems' transitive axioms. The graph-level conclusions use only propext, Classical.choice, and Quot.sound. The manifest includes the original repository path for every published dependency in vjdad4m/maths.

[Complete pinned Lean sources](proof-sources.tar.gz). Extract the archive and use its replay script.
