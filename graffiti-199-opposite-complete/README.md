# graffiti-199-opposite-complete

For a finite simple graph with connectivity at least three and induced tree number at most five, take a three-cut {r,a,b} with two connected shores X and Y. Suppose r misses a vertex of Y, a is complete to Y, and two components of the nonneighbors of r in X each have a sole contact among its neighbors in X. The graph has a Hamiltonian path. Theorem traceable_of_two_private_components_complete_opposite allows arbitrary order and arbitrarily many additional nonprivate components. It derives the two-contact condition for every other component.

The 900 interface tests are optional and use the Python standard library. All graph claims in the theorem are checked by Lean.

## Verification

In a shell with Lean 4.19.0 available, set GRAFF199_MATHLIB to the Mathlib v4.19.0 checkout with its standard compiled library. GRAFF199_LEAN_BIN may point to the toolchain bin directory. Run from this package directory.

```sh
bash replay.sh
```

The script checks the pinned versions, validates every listed SHA-256, compiles all sources in dependency order with warnings as errors, and prints the final theorems' transitive axioms. The graph-level conclusions use only propext, Classical.choice, and Quot.sound. The manifest includes the original repository path for every published dependency in vjdad4m/maths.

[Complete pinned Lean sources](proof-sources.tar.gz). Extract the archive and use its replay script.
