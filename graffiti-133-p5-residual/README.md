# Graffiti.pc #133: nested P5-free core and the private C5 atlas

**Partial results.** In the connected, C4-free, induced-P9-free high-mean branch at radius at least four, Lean reduces the problem to radius four and a nested minimum connected dominating core. Its innermost, induced-P5-free graph is either a spanning 5-cycle or has a dominating clique with unique anchors and matching edges inside anchor fibers. The clique has order at most three. The radius statement is a restricted formal proof of a consequence of the known Erdős–Saks–Sós induced-path theorem, not a priority claim.

In the spanning 5-cycle branch, choose a private neighbor for each cycle vertex in the middle core and then a private neighbor for each chosen vertex in the full graph. Lean checks the possible adjacency masks of both chosen layers. The five outer vertices induce a matching; an edge can occur only when the first layer gives the Petersen case, and only between cyclically adjacent sites. [Formal reduction](src/P5NestedHighMeanInnerShape133.lean) · [Checked private-layer atlas](src/P5PrivateAtlasStrongFinal133.lean)

This does not settle the ambient score or full #133. Replay in a prepared Lean/Mathlib 4.19.0 checkout using `lake env bash /path/to/maths/graffiti-133-p5-residual/replay.sh`. [Strict compiler transcript](StrictReplay.log)
