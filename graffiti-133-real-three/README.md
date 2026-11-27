# Graffiti.pc #133 for unrounded local-independence mean at most three

The [main theorem](src/UnroundedBand133.lean) proves the unrounded bound for every finite connected graph with average neighborhood independence at most 3, with no radius, cycle or regularity assumption. When there is no four-cycle the bound is radius plus the exact mean. The formal statement also includes the simpler radius bound when a four-cycle is present. This does not settle the general conjecture.

The key lemma says that in a connected four-cycle-free graph, a mean strictly above 2 forces an induced six-vertex path or radius at most 2. With no five-cycle, deletion of local-independence-one vertices preserves the strict density threshold and leaves a graph where an induced six-vertex path can be constructed. With a five-cycle but no induced six-vertex path, the pentagon dominates the graph. A check of the possible contacts of two adjacent exterior vertices shows that if their pentagon contacts differ then one pentagon vertex is within distance 2 of every vertex. Otherwise the exterior edges stay within single-contact classes and summing local independence over the graph gives a mean at most 2.

Two [additional bounds](src/MoreBands133.lean) cover the exact real mean at most 4 and the floor mean at most 4 when radius is at most 2. In that case, a mean strictly above 3 always forces an induced six-vertex path in a four-cycle-free graph.

See [the density release](../graffiti-133-density) for references and [the floor-three release](../graffiti-133-floor-three) for the separate rounded statement. This is a Lean verification; we make no priority claim.

## Replay

From a Lean 4.19.0 project with the Mathlib 4.19.0 build cache:

    lake env bash /path/to/maths/graffiti-133-real-three/replay.sh
