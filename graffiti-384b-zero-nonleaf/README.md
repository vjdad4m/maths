# Graffiti.pc #384b whenever a nonleaf lies in no triangle

For every finite simple graph G, if a vertex lies in no triangle and has degree at least two, then γ₂(G) ≤ n − ⌈|T|/2⌉. The theorem allows disconnected graphs and every order. Combining this with the positive-palette theorem, a connected counterexample to the catalogue statement must have odd diversity and realize zero only on leaves. The remaining leaf case is open here. [ZeroLeaf384b.lean](ZeroLeaf384b.lean)

For any putative failure, a degree-two vertex z with zero triangles and a count-one vertex e have four distinct neighbors. In the spanning graph J consisting of triangle edges plus the two edges at z, delete e and z. There are two vertex-disjoint simple paths from the two neighbors of e to the two neighbors of z. The correspondence between the endpoints is determined by the paths. Every edge of either path belongs to a triangle in the original graph. [OriginalArms.lean](OriginalArms.lean)

To obtain the paths, let A and B be the neighbor sets of e and z. In the remaining graph match each vertex outside B to itself or an adjacent vertex outside A. For a subset X of the domain, a failure of Hall's inequality would leave fewer than two vertices separating e from z. This contradicts the deletion theorem. Hall's theorem therefore gives an injective matching. [HallArms.lean](HallArms.lean)

Starting at either vertex of A, iterate the matching until the first visit to B. An earlier repetition would contradict injectivity since a start has no predecessor. The same cancellation excludes intersections between the two trajectories. [OrbitArms.lean](OrbitArms.lean)

The module HallFiniteBase reproduces the pinned Mathlib file `Mathlib/Combinatorics/Hall/Finite.lean` byte for byte under a local module name. Its SHA-256 is `9cc20c593653b25aac64e2085d1311e3b0c042b51ad02d984527962785c4583f`. The checked entry point authenticates this file directly against Mathlib at commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`.

If the arms have the same length parity, they close an even cycle through e and z. Otherwise each triangle witness on the last edge of the first arm must lie on the second arm. A witness outside it would permit rerouting to change the first arm’s parity. The terminal edge always has such a triangle after e,z are removed, and the witness lies strictly before the other endpoint because the neighbors of z are nonadjacent. [ParityArms.lean](ParityArms.lean) · [TerminalArms.lean](TerminalArms.lean)

Choose a pair of arms of minimum total length over both endpoint pairings. Each of the two terminal witnesses can redirect a prefix to the other terminal. Minimality forces both witnesses to be the penultimate vertices. These vertices u and v are adjacent and both see the final vertices c,d. The two prefixes joined through e and closed with u–v give an even cycle. The square z–c–u–d–z meets it only at u. Their alternating colorings can be aligned at u. A maximum cut with those colors fixed protects both e,z and every high vertex. This contradicts equality in the frozen positive-palette bound. [ShortestArms.lean](ShortestArms.lean) · [CycleSquareArms.lean](CycleSquareArms.lean)

The entire linkage and parity argument in the older LINKAGE-NOTE is now formalized. We audited the parallel #189 sources HallLinkage189.lean, HallOrbit189.lean and HallBoundaryTransfer.lean. The global-connectivity #189 theorem has a stronger hypothesis. The local boundary transfer provides an alternate proof using a permutation on slot and vertex copies. Our already checked matching maps the complement of the final neighborhood into vertices outside the first neighborhood and its orbit extraction returns the exact indexed routes needed by the parity proof. The common imported theorem is Mathlib’s finite Hall theorem. No #189 object is required for this release.

## Parity and the pendant-ear split

Every pair of disjoint arms in a failure has opposite length parity. Equal parities would close an even cycle through both designated vertices. [ParityArms.lean](ParityArms.lean)

If the triangle-edge graph has exactly |T|−1 vertices of degree at least three, all positive-score vertices have degree at least three there, positive scores are injective, and every zero has original degree at most one. Also, two adjacent degree-two triangular ears exhaust all count-one vertices of a failure. A third ear beyond their anchor contradicts the cut-vertex theorem. If the third count-one vertex were the anchor, the three degree-two vertices form a triangle component containing exactly one protected representative, which contradicts component parity. This proof works for disconnected original graphs. Identical anchor pairs are already settled without a diversity hypothesis by the frozen predecessor theorem `Repair.exact_of_twin_degree_two`. [PendantAudit.lean](PendantAudit.lean)

## Replay

The source archive includes the exact 14-module baseline source archive and ten supplement modules, including the unmodified Mathlib Hall file. Run the entry point with these environment variables.

~~~sh
export CROSSFOUR_LEAN_BIN=/absolute/path/to/lean-4.19.0-linux/bin
export CROSSFOUR_MATHLIB=/absolute/path/to/built/mathlib4
python3 -B replay_linkage.py
~~~

The default command cold-replays the baseline archive and then compiles the ten supplementary modules. To reuse a completed baseline replay, pass `--baseline-log /absolute/path/to/StrictPackedCold.log`. This mode verifies all 38 baseline object hashes and recompiles the ten supplement modules. Both modes check the expected object hashes, warnings as errors and standard axioms. [Replay entry point](replay_linkage.py) · [Source hashes](SOURCES.sha256) · [Object hashes](OBJECTS.sha256)

[Complete pinned Lean sources](proof-sources.zip). Extract the archive and use its replay script.
