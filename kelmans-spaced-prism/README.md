# Kelmans: spaced-prism obstruction to uniformly bounded local repair

For every proposed bound B, there is a finite simple cubic, cyclically four-edge-connected and 3-vertex-connected host with a valid remote deletion/omission board and an admissible smaller-rank source factor. The canonical image of **that** source factor cannot be completed by B or fewer one-hole slides followed by one one-tile cleanup. Nonetheless, every board in this constructed family has an explicit full factor of three-vertex paths.

The board is obtained by subdividing six well-separated rungs of a prism. A horizontal source factor leaves the six subdivision slots empty. The [separated-vacancy bound](../kelmans-remote-dependencies/README.md) excludes every repair sequence below the requested length, even if it is not monotone. The final factor is built separately using subdivision-centered paths and horizontal intervals. This is an obstruction to a uniform bound over arbitrary rank outputs, **not** a counterexample to the Kelmans conjecture and **not** a claim that all choices of source factor fail.

See [the end-to-end theorem](src/RemoteSpacedPrismObstruction.lean) and [the explicit final factor](src/PrismSpacedFinal.lean). The project passed an independent strict Lean 4.19.0 modular replay, and the displayed axiom reports use only the standard axioms.

Compile with Lean 4.19.0 and Mathlib 4.19.0. Build the dependencies from the [square](../kelmans-square-f2/), [handle](../kelmans-handle/), [remote completion](../kelmans-remote-t2-bridge/), and [repair](../kelmans-remote-dependencies/) packages, and make their module objects visible on `LEAN_PATH`. Then build the nine source modules in the order given in `modules.txt`. The SHA-256 manifest records the exact checked sources.
