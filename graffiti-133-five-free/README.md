# Graffiti.pc #133: the next unrounded bands without five-cycles

Two Lean results extend the [unrounded mean-three result](../graffiti-133-real-three) to connected graphs with no simple five-cycle:

- [Radius at most 2, exact mean at most 5](src/SeventhNoFive133.lean).
- [Radius at most 3, exact mean at most 4](src/NoFiveSeventh133.lean).

The structural lemma behind the second result is that a connected graph with no four- or five-cycle and mean local independence at least three contains an induced seven-vertex path. Peeling vertices of local independence at most one preserves connectivity and the density threshold. If a longest induced path in the core has fewer than seven vertices, an extra independent neighbor of an endpoint either lengthens it or creates an induced hexagon or heptagon. Attachment restrictions in the two cycle cases force the mean below three if no induced seven-vertex path exists.

The hypothesis excludes all simple five-cycles, not just induced ones. These results do not yet cover graphs with five-cycles at those thresholds, or the general conjecture.

## Replay

From a Lean 4.19.0 project with the Mathlib 4.19.0 build cache:

    lake env bash /path/to/maths/graffiti-133-five-free/replay.sh
