# Kelmans: a fixed partner-swap obstruction

**Partial structural result, not a resolution of the Kelmans conjecture.** Assume the graph has at least seven vertices and that every cut with at most three edges has a side of size at most one. Five vertices of degree at most three cannot span a copy of (K_{2,3}) as a subgraph: the two hubs have no neighbors outside those five, so there are at most three boundary edges.

The Lean development derives two consequences for cubic graphs under this cut condition:

* No two vertices have the same open neighborhood.
* Two distinct neighbors of a vertex cannot be interchanged by a map that fixes all other vertices and preserves edges on the remaining graph, even after deleting the common neighbor and any one additional vertex other than the partners.

This rules out a fixed relabeling in one approach to choosing the partner at the center of a (P_3). It does not rule out moving additional vertices or changing individual tiles.

Replay [TwinObstruction.lean](src/TwinObstruction.lean) with `lake env lean -DwarningAsError=true /path/to/maths/kelmans-twin-obstruction/src/TwinObstruction.lean` in a Lean and Mathlib 4.19.0 project.
