# Graffiti.pc #133: the seven-cycle branch of the induced-path bound

**Partial result.** Lean proves that a connected graph with no four-cycle, no induced six-cycle, an induced seven-cycle, and local independence at least two at every vertex either has an induced path on seven vertices or has average local independence strictly below three. This excludes the seven-cycle branch of a minimum-local-independence reduction. It does not treat graphs containing an induced six-cycle.

The statement and proof are in [C7OnlyMain.lean](src/C7OnlyMain.lean), theorem `sum_lt_three_of_hole_seven_no_six`.

In a Lean and Mathlib 4.19.0 project, run `lake env bash /path/to/maths/graffiti-133-seven-cycle/replay.sh`.
