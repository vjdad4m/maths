# Graffiti.pc #133: nested two-control case without a crossing cap

Let the host be a finite connected graph with no ordinary four-cycle and no induced nine-vertex path, and with radius at least four. Suppose it has a minimum connected dominating induced subgraph consisting of a seven-cycle and two control vertices, with no induced seven-vertex path in this subgraph. Suppose furthermore that the cycle-near base satisfies the stated C7 domination condition and has at most four vertices with multiple cycle contacts. Then the **whole host has mean local independence at most four**, with no numerical restriction on the edges between the near base and the remainder.

[Exact main Lean theorem](src/NestedCoreMinimumTwoCoreUnlimited133.lean) · [Axiom transcript](StrictReplay.log) · [Source hashes](sources.sha256)

The proof derives nine private witnesses from minimality of the inner core and handles both contact archetypes automatically. A finite, verified obstruction shows that each deleted short crossing can be charged to a distinct triangle. Removing those edges cannot reduce the local-independence sum by more than the available budget. The radius argument leaves at most three retained exceptional gates and the earlier three-gate proof applies without a bound on the original crossing degrees.

This is a partial result: the near-base multi-contact hypothesis, the specified form of the minimum inner core, and the other remaining scopes of #133 are not removed. The finite certificates are verified by Lean; no external search result is an axiom.

Replay with Lean 4.19.0 and prepared Mathlib 4.19.0: `lake env bash /path/to/maths/graffiti-133-nested-two-control-unlimited/replay.sh`.
