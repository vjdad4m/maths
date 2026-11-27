# Graffiti.pc #133: minimum two-control core without numerical caps

Suppose a finite connected graph is C4-free and induced-P9-free and has radius at least four. Suppose a minimum connected dominating induced subgraph is induced-P7-free and consists of an induced seven-cycle plus two vertices that touch that cycle. Then the whole graph has mean local independence at most four. [Precise Lean statement](src/NestedCorePrivateMinimumTwoCoreNoCap133.lean).

Unlike the [previous result](../graffiti-133-nested-two-control-unlimited/README.md), this proof does not assume a bound on how many vertices touch the cycle more than once, or on edges crossing out of the near base. The needed decomposition is constructed internally. The proof uses the private witnesses supplied by minimality, 80 kernel-checked local obstructions, and refined weighted bounds on adjacent and far cycle-contact profiles. These leave at least five units of slack in the near base, enough for the previously checked transfer after removing the paid crossings.

This is a partial result for the stated core structure, not a proof of all Graffiti.pc #133. Replay with Lean and Mathlib v4.19.0 from a prepared Mathlib checkout: `lake env bash /path/to/maths/graffiti-133-nested-two-control-no-cap/replay.sh`. The [modular transcript](StrictReplay.log) records only standard axioms.
