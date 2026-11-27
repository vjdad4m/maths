# Graffiti.pc #199: uniform missed components and a private-contact splice

Two Lean-checked results preserve the last work from this paused lane.

- [Uniform missed component exclusion](UniformMissExcluded.lean): in the reduced minimum-counterexample branch at exact connectivity three with independent cubic vertices and at least three misses, a nonsingleton missed component with uniform ordinary contacts is excluded.
- [Independent-miss path splice](IndependentMissRoute.lean): in the stated cut configuration, two private ordinary contacts for each miss, with the two outside ports meeting distinct misses, suffice for an original-graph Hamiltonian path.

Use the Lean 4.19.0 and Mathlib 4.19.0 settings and the frozen dependency overlay in the [199-module missed-components package](../graffiti-199-miss-components). Compile the following new modules in order: HubDeletion, HubTorso, HubLift, HubExpansion, IndependentMissRoute, UniformMissExcluded. The individual check logs record replay with warnings as errors against the frozen objects and show only standard axioms for the principal results. The full clean-source rebuild was not finished when this lane was paused. This release omits the unchecked Hall extension. The general conjecture remains open.
