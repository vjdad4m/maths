# Graffiti.pc #189: all graphs with d≥36 and connectivity at least d−2

Let G be a finite connected simple graph and k≥34. Assume each vertex
has at most k+3 even-distance vertices (including itself), deletion of
fewer than k vertices preserves connectivity, and for every two
distinct vertices at least one has degree at least k+2. Then G has a
spanning path. Setting d=k+2 gives the stated complete subdomain of #189.
This does not settle smaller degree or unrestricted connectivity.

After the earlier attachment classification, only an oversized
single-pin cut might survive. A cut of size k+1 supplies Hall with
deficit at most one and yields a root-deleted 2-connected shore.
The earlier formal circumference theorem gives terminals routes of
order at least k−1. The weighted disjoint hooks then need one of two
ways to account for the cut: a pin-adjacent nonpin cut port saves most
of a distance-two budget in the order upper bound, or else at most eight
nonpin cut ports lie on the longest path. In either case the lower
order bound from spacing the hooks contradicts the upper bound.

Replay with Lean/Mathlib 4.19 and prior #189 theorem objects including
the exact-cut one-pin and one-low circumference certificates on LEAN_PATH.
