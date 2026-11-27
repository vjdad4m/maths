# Graffiti.pc #189: components whose distance-two budget is exhausted

Let P be a longest path in a finite connected simple graph. Take a
vertex x omitted by P and let H be its component off P. If every
distance-two vertex from x is a path flank of one of its contacts
with P, then H is exactly the off-path closed neighborhood of x.
Moreover the path contacts of H are exactly the contacts of x.

In particular this applies when x has two contacts at least three
positions apart and its distance-two neighborhood has at most four
vertices. The four distinct flanks exhaust that budget. There is no
component-order restriction and no need for the remaining degree or
cut hypotheses of the catalogue problem.

The main theorem is
`Graffiti189LongestPath.OmittedSaturation.component_eq_star_and_contact_eq_of_saturated_flanks`.
This reduction does not settle the five-omission branch of the
16-vertex case or the general conjecture.

Use Lean 4.19.0 and Mathlib at
`c44e0c8ee63ca166450922a373c7409c5d26b00b` on `LEAN_PATH`.
From the repository root run `bash graffiti-189-saturated-flank-components/replay.sh`.
