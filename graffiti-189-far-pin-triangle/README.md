# Graffiti.pc #189: far-singleton triangle reduction

Strict Lean partial, without an upper-order hypothesis. At threshold d≥6 and connectivity at least d−2, a high-degree omitted root with one path pin and a fourth-shell vertex can be part of a hypothetical counterexample only if:

1. its omitted-star boundary has size d−2;
2. the remaining shore outside the star and its boundary is connected;
3. the pin and its two immediate path flanks form a triangle; and
4. the omitted star has order d or d+1.

The connectivity and triangle restrictions exclude whole structural cases at arbitrary graph order. The single remaining connected-triangle far-singleton branch, other omission models, and the full conjecture are not claimed solved.

* [FlankIllumination189](src/FlankIllumination189.lean): Choose either flank f of the sole pin t. If m cut ports other than t see neither t nor f, then n≤3d+1+md. This closes m=0 for d≥7 and m≤1 for d≥10; a vertex behind a port seen by f at distance two is charged to f's existing even-distance budget, or else is charged to t if it sees f directly.
* [FlankShore189](src/FlankShore189.lean): The only adjacency from t to the complementary shore consists of its two path flanks; every complementary component must contain one. A missing t contact would reduce the cut below d−2.
* [SplitFlankImpossible189](src/SplitFlankImpossible189.lean): If two complementary components remain, each meets t in exactly one flank and is large by the previous small-shore exclusion. For a high flank f, q adjacent cut ports charge q distinct distance-two vertices in the other component. Partition the star into L (vertices adjacent t) and T (the others). The distance-two budget of f then says |L|+q≤d and hence q≤|T|. The budget of t charges |T| along with the local neighbors of both flanks; high degree at f and at least one internal neighbor of the opposite flank give q>|T|, a contradiction.
* [TriangleFar189](src/TriangleFar189.lean): If one high flank sees q cut ports and |L|+q>d, the complementary shore has radius at most two from that flank, since a farther vertex would lie behind a smaller separator. This forces n≤3d, below the preceding order floor. The only potential nontriangle equality makes the other flank's complementary neighbors a subset of the high flank's neighbors. It cannot border the far set, so erasing it saves the last separator slot and again forces radius two. The adjacent-flank case needs star size at most d+1 to avoid the same budget obstruction.

Lean/Mathlib 4.19.0. Build the prior lock, fourth-shell and cut-geometry modules including TruncatedHall189 and ExactStarOpposite189. Put precompiled dependencies on LEAN_PATH and run replay.sh. The fresh replay checks hashes and compiles with warnings as errors.
