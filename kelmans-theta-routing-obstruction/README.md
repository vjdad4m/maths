# Kelmans: a fixed theta routing can fail

**Obstruction to one proof route, not a counterexample to F2 or Kelmans.** Lean checks a 16-vertex cubic graph in the required cyclic-four and cyclic-five cut classes. It contains the exact labelled seven-vertex theta from [the conditional packing theorem](../kelmans-theta-f2/README.md), but both prescribed exterior contact pairs are adjacent. With those fixed port roles, the cap has a forbidden three-edge cut.

The deletion target itself still has an explicit (P_3)-factor into five paths. The obstacle is therefore to transporting a factor through that particular capped graph, not to the desired factor existing.

See [the finite graph and factor certificate](src/ThetaFixture.lean) and [the graph isomorphism and cap obstruction](src/ThetaFixtureLayout.lean). Run `lake env bash /path/to/maths/kelmans-theta-routing-obstruction/replay.sh` in Lean and Mathlib 4.19.0.
