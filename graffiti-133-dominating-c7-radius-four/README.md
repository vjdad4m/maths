# Graffiti.pc #133: a dominating induced seven-cycle at radius at least four

Let the finite connected graph contain no four-cycle and no induced
nine-vertex path. Assume an induced seven-cycle dominates the whole
graph. If the radius is at least four, average local independence is
at most four. Exterior contacts and triangles are unrestricted.

The proof uses the exact four-cycle-free identity
`sum(local independence) + 3 * triangles = 2 * edges` and 14 units
of slack for single contacts. At radius at least four, there are no
three-contact profiles; there are at most seven neighboring
two-contact profiles and at most three distant ones. Their total
charge is at most 13.

Main theorem: `Graffiti133MultiWeighted.radius_four_dominating_C7_mean_four`.
This does not address domination of a proper core alone, or the
general conjecture.

Use Lean 4.19.0 and Mathlib at
`c44e0c8ee63ca166450922a373c7409c5d26b00b` on `LEAN_PATH`.
Run `bash graffiti-133-dominating-c7-radius-four/replay.sh` from the repository root.
