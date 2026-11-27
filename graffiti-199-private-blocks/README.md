# Graffiti.pc #199: private components and prescribed half-paths

These Lean results concern a three-vertex cut in a 3-connected graph with no induced tree on six vertices. If a port r misses a vertex in the opposite component, there are at most two private components on the studied side: these are the components off the neighbors of r that have just one contact back to a neighbor of r.

Each of the two other cut vertices must meet every private component. Three such components would force an induced tree on six vertices, either by extending a star into the opposite side or using the adjacency pattern between r and the star center. Under the stated rooted block hypotheses, two private cliques give a spanning half-path between prescribed ends in those cliques. A separate lemma bounds the independence number of the opposite component when a port is complete to it.

[At most two private components](PrivateComponents.lean) · [Prescribed half-path](PrivateHalfFromGeometry.lean)

These are unrestricted-order structural results in the stated scope. The whole-graph splice and full #199 are not asserted here. The new modules passed Lean 4.19.0 with warnings as errors and only the standard axioms. Build dependencies from [mixed cubic cuts](../graffiti-199-mixed-cubic-cut/) and [order-eleven cuts](../graffiti-199-order-eleven/) first, then follow the exact module order and hashes in `PrivateBlocksManifest.tsv`.
