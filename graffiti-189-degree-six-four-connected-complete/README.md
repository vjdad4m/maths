# Graffiti.pc #189 at degree six and vertex connectivity at least four

**The full subcase is proved in Lean**, with no graph-order restriction.
Let G be a finite connected simple graph with second-smallest degree
exactly six, counting ties, and with at most seven vertices at even
shortest-path distance from each vertex, including itself. If deleting
fewer than four vertices preserves connectedness, then G has a spanning
simple path.

Main declaration: `Graffiti189LongestPath.traceable_at_degree_six_four_connected`.
The unrestricted Graffiti.pc #189, including degree six at connectivity
two or three, does not follow from this theorem.

## Proof structure

1. The parity cover bounds the order by 25. The prior exact
   order-24 theorem supplies a spanning path up to order 24.
2. At equality, a minimum first-layer cover yields t in {3,4}, b in
   {4,5,6}, and an exact partition of the third layer with private
   middle witnesses and saturated distance-two budgets. The graph is
   explicitly relabelled on Fin 25. The Lean semantic transfer proves
   all the hypotheses of the finite profile, not just the order counts.
3. Kernel-checked RUP proof terms refute the six normalized profiles.
   The CNF interpretation is checked in Lean. No SAT solver is called
   during replay and no native decision or custom axioms are used.

## Replay

Use Lean and Mathlib 4.19.0. Before running `replay.sh`, put the verified
predecessor objects on LEAN_PATH, including
[SixFourOrderTwentyFour189](../graffiti-189-degree-six-four-connected-twenty-four/)
and [SixFourFiniteOrder189](../graffiti-189-degree-six-four-connected-finite-twenty-five/)
and their dependency closures (`certificates/DEPENDENCIES.txt` in the
certificate package explains the graph SAT prerequisites; the directory
inside this archive is named `certificates/`).
The strict graph and certificate transcripts accompany the sources.
Frame 36 is the largest and may take several minutes to replay.

[Complete pinned Lean sources](proof-sources.zip). Extract the archive and follow the replay instructions.
