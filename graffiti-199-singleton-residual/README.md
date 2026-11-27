# Graffiti.pc 199 — separating three-sets and singleton components

This is an arbitrary-order partial result for the *Written on the Wall II* conjecture that a connected finite simple graph of order at least two has a Hamiltonian path when the order of its largest induced tree is at most its vertex connectivity plus two.

## Main statements

* `traceable_of_three_or_more_components` in [FourRoutes.lean](src/FourRoutes.lean) proves that vertex connectivity at least three and largest induced tree of order at most five imply a Hamiltonian path whenever some three-vertex deletion leaves at least three components. Singleton components count. This theorem uses neither minimality nor any restriction on the cubic vertices.
* `catalogue_minimum_port_deficiency` in [CatalogueSingleton.lean](src/CatalogueSingleton.lean) works at exact vertex connectivity three, order at least five and the catalogue tree bound. The graph is assumed nontraceable, its degree-three vertices are independent, and every strictly smaller connected graph of order at least two satisfying the catalogue bound is assumed traceable. A separating three-set exists. For **every** separating three-set, its deletion leaves a singleton z and a connected shore X. The cut is precisely the open neighborhood of z. The theorem quantifies over every ordering of its three vertices.
* Each cut vertex roots a four-vertex induced tree meeting X in the other three vertices. No such rooted five-vertex tree exists. For any such quartet, an outside vertex of X meeting it has at least two contacts and each of the other two cut vertices has at least one. Four independent vertices in X can be chosen simultaneously so that every cut vertex misses at least one of them. [ExactResidual.lean](src/ExactResidual.lean)
* At least two of the three cut vertices each have at least two distinct nonneighbors in X. A cut vertex with a unique nonneighbor x in X forces x to be cubic and adjacent to the other two cut vertices. The main theorem expresses the counting assertion by quantifying over every pair of distinct cut vertices. [CatalogueSingleton.lean](src/CatalogueSingleton.lean)
* For the single exceptional cut vertex, x has a unique neighbor p within X. The vertices in X other than x and p that miss p form a clique. The graph on X without x has no spanning path. These are conclusions of `SingletonCut.single_miss_core` under the explicit singleton-cut, deletion-path and one-nonneighbor hypotheses. [SingleMissCore.lean](src/SingleMissCore.lean)

All named theorems above are in `Graffiti199Depleted.Catalogue.Incomplete`. The catalogue interface includes a proof that its spanning-walk predicate agrees with Mathlib's Hamiltonian-walk predicate.

## The two-port splice

`SingletonCut.traceable_of_two_almost_complete` assumes the finite graph has connectivity at least three, the induced-tree bound five, a singleton cut with connected shore X, and a spanning path after deleting z. If two ports r and a each miss at most one vertex on X, the whole graph has a spanning path. The main theorem obtains the deletion path from minimum order and independence of the cubic vertices.

In the nontraceable case, call the missing vertices x and y. Deletion-path rotations force x to be adjacent to a and b, and y to r and b. Substituting z for x along a deletion path and applying the forbidden six-vertex star proves that x is cubic. The same holds for y, and they are independent. Write p for the unique ordinary neighbor of x. In the remainder R of X after deleting x, y, p, any independent triple together with x and z would give five independent neighbors of a. The connected shore supplies an edge from p into R. The existing prescribed-endpoint lemma spans R together with a starting at that contact. Prefixing the path z, r, y, b, x, p gives a Hamiltonian path. The Lean proof also derives nonemptiness of R. [UniqueMissDegree.lean](src/UniqueMissDegree.lean) · [DoubleMissSplice.lean](src/DoubleMissSplice.lean)

## Source and replay

The first 107 files in the ordered [manifest](Manifest.tsv) reproduce the frozen surviving-edge crossing package byte for byte. The bundle also reuses four omission-path source files from the cubic-contraction and flank packages, the terminal-flank prefix of `FlankAttachment.lean`, and the existing prescribed-endpoint route for a universal vertex and a set of independence at most two. Provenance and SHA-256 values are recorded per source. An order-eleven census is unnecessary for this argument.

Use Lean 4.19.0 and a compiled Mathlib v4.19.0 checkout at commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. From the package directory run

```sh
GRAFF199_MATHLIB=/path/to/mathlib4 GRAFF199_LEAN_BIN=/path/to/lean-4.19.0-linux/bin bash replay.sh > StrictReplay.log 2>&1
python3 audit.py
```

The script builds all 132 project modules in a fresh temporary directory with warnings as errors and asynchronous elaboration disabled. The source audit checks the digests, compile order, forbidden proof tokens, and axiom outputs. Recorded results are in [StrictReplay.log](StrictReplay.log) and [FinalAudit.log](FinalAudit.log).

The remaining branch allows all three ports to have at least two ordinary nonneighbors, or exactly one port to have a unique nonneighbor with the structure above. Traceability in these configurations, the complete connectivity-three case, and general #199 remain open in this work.

[Complete pinned Lean sources](proof-sources.tar.gz). Extract the archive and use its replay script.
