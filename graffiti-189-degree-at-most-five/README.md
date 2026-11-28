# Graffiti.pc #189 at second-smallest degree at most five

The conjecture holds for finite connected simple graphs of second-smallest
degree 1, 2, 3, 4, or 5. This single Lean theorem combines the verified
[degree-one and degree-two argument](../graffiti-189-degree-one-two/),
[degree three](../graffiti-189-degree-three/),
[degree four](../graffiti-189-complete-degree-four/), and
[degree five](../graffiti-189-degree-five-complete/). The original conjecture
at higher degrees is not resolved by this package.

The [final declaration](DegreeAtMostFive189.lean) uses the even-distance cap,
the condition that all but at most one vertex have degree at least d, and the
existence of a vertex of degree at most d. These follow from the catalogue
conditions when d is the actual second-smallest degree.

With the above dependency objects (including the Mathlib RUP checker and
the ArticulationClique189 compatibility overlay) on LEAN_PATH, replay under
Lean and Mathlib 4.19.0 with
`lean -j1 -DElab.async=false -DwarningAsError=true DegreeAtMostFive189.lean`.
The [verification transcript](VERIFIED.log) reports only standard axioms.
