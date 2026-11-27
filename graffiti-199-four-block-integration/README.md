# Graffiti.pc #199: integrating four-loss two-singleton configurations

**Partial result.** Under the explicit four-block packing and cut hypotheses, Lean excludes the four-loss two-singleton branch at orders 15 and 16. The argument proves the identity

`order + singleton overlap + terminal losses = 16`.

At order 15 the proof also handles a shared high vertex of the two singleton blocks. [The final theorem](src/CatalogueInterface.lean) uses the same connectivity and traceability predicates as the public low-connectivity proof. [The counting and integration lemmas](src/FourBlockIntegration.lean) state the exact assumptions.

The missing reduction is to derive the four-block cover, allocation membership and crossing law from an arbitrary minimum counterexample. This package does not prove that reduction or the full conjecture.

Use Lean and Mathlib 4.19.0 and run `lake env bash /path/to/maths/graffiti-199-four-block-integration/replay.sh`. The replay uses the earlier published configuration and overlap packages as dependencies.
