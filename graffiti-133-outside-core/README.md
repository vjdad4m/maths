# Graffiti.pc #133: bounds outside a dominating core

**Structural partial results.** In a graph with no ordinary four-cycle, let (C) be a dominating set.

- The graph induced by vertices outside (C) has maximum degree at most (|C|). Assign a neighbor in (C) to each exterior neighbor of a given exterior vertex. Two neighbors cannot receive the same assignment without forming a four-cycle.
- At most (inom{|C|}{2}) outside vertices have two or more neighbors in (C). Each such vertex can be assigned a distinct pair of core vertices. In particular, a core of size at most nine allows at most 36 such outside vertices.
- If the host has no induced nine-vertex path, any connected induced exterior subgraph has order at most (sum_{i=0}^{7}|C|^i). This is a bound on each component, not on the total number of exterior vertices or components.

These inequalities help describe the graph around a small dominating core in the mean-five branch, but do not settle its density bound. See [the neighborhood counts](src/OuterCoreBounds133.lean) and [the component bound](src/OuterComponentOrder133.lean).

Replay in Lean and Mathlib 4.19.0 with `lake env bash /path/to/maths/graffiti-133-outside-core/replay.sh`.
