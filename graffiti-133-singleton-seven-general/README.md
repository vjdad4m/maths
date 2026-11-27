# Graffiti.pc #133: dominating induced seven-cycle with singleton contacts

For a finite simple graph with no four-cycle (induced or not) and no
induced path on nine vertices, assume there is an induced seven-cycle
and every vertex off it has exactly one neighbor on it. Then the
average local independence number is at most four. This is the
inequality `∑ v, localIndependence G v ≤ 4 * |V|` in Lean.

There is no assumption on exterior triangles. Distinct exterior
triangles cannot intersect, and three disjoint exterior triangles
would force an induced nine-vertex path. The latter proof relabels
the cross-edge endpoints independently on each triangle, retaining
only 30 normalized models. With at most two exterior triangles, the
previous bound applies.

The main theorem is
`Graffiti133ExteriorTriple.singleton_seven_mean_four`. The general
conjecture and the regime with multiple contacts are not resolved.

Use Lean 4.19.0 and Mathlib at
`c44e0c8ee63ca166450922a373c7409c5d26b00b` on `LEAN_PATH`.
Run `bash graffiti-133-singleton-seven-general/replay.sh` from the
repository root.
