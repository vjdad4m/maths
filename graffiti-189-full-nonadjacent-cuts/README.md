# Graffiti.pc #189: every nonadjacent two-cut at the degree-five threshold

Let G be finite, simple and connected, remaining connected after deletion
of any one vertex. Assume at most one vertex has degree below five and
every even-distance set, counting its center, has at most six vertices.
If G has a two-vertex separator consisting of nonadjacent vertices, then
G has a spanning path. No order, cut-degree, component-count, or
attachment-pattern restriction is imposed on this theorem.

Reuse the exact distance-two proof. Every remaining nonadjacent cut is
at distance three and has endpoint degrees between five and eight.
The degree-six branch is completed here, including the one-bridge and
two-bridge balanced cases. Local closure edges are eliminated before
combining routes in the original graph.

[Main theorem and distance-three corollaries](DegreeFiveNonadjacentComplete189.lean)
· [Strict replay](StrictReplay.log)

Build the earlier degree-five cuts, degree-five more cuts, cross-saturation,
full distance-two, distance-three high-cut, and degree-seven/eight packages
using Lean/Mathlib v4.19.0. Keep their object roots on LEAN_PATH and run
the replay script in the archive. The new source cone and direct Git-blob
pins are included. Use the archive's renamed degree-six module rather than
importing objects from the earlier unbalanced degree-six package.

This proves a complete cut subdomain, not unrestricted #189.

[Complete pinned Lean sources](proof-sources.zip). Extract the archive and use its replay script.
