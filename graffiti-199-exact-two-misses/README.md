# Graffiti.pc #199 — two ordinary nonneighbors at connectivity three

## Scope

Let a finite simple graph have connectivity at least three and no induced tree on six or more vertices. Deleting the three neighbors $r,a,b$ of a degree-three vertex $z$ leaves $z$ and one connected component $X$. An ordinary vertex belongs to $X$.

The graph-level theorem `SingletonCut.traceable_of_exactly_two_misses` assumes that $G-z$ has a Hamiltonian path and that any two surviving edges lie in the same component after deleting at most three vertices. If $r$ misses exactly two distinct ordinary vertices, then $G$ has a Hamiltonian path. The proof covers all configurations of their mutual edge and of their edges to $a,b$. [Graph theorem](src/ExactTwo.lean)

The integrated theorem `catalogue_minimum_all_ports_miss_three` assumes a nontraceable graph of exact vertex connectivity three, order at least five, independent degree-three vertices, the catalogue induced-tree bound, and traceability of every smaller connected graph of order at least two meeting its own catalogue bound. It derives the deletion path and the surviving-edge property from those hypotheses. Cubic independence enters at this upstream step. A separating triple exists. In every separating triple, **each port misses at least three distinct ordinary vertices**. The simultaneous independent quartet and rooted-tree conclusions from the baseline are retained. Both theorem names use the namespace `Graffiti199Depleted.Catalogue.Incomplete`. [Catalogue statement](src/CatalogueThreeMisses.lean)

The branch in which every port misses at least three vertices, the full connectivity-three claim and the unrestricted conjecture remain open in this work.

## Why the restriction on the two misses matters

* A path in $X$ joining an $a$-contact to a $b$-contact closes up with $a,z,b$ to form a cycle. Reserve its vertices. If all unused ordinary vertices see $r$, failure of traceability forces those unused vertices into three mutually anticomplete nonempty cliques. Opening the cycle at two consecutive vertices lets the proof join distinct cliques through the reserved vertices. An ordinary $r$-neighbor on the path touches at least one clique. An ordinary $r$-nonneighbor touching any clique touches a second. This argument uses the six-vertex tree bound and actual edges. [Reserve cycle](src/ReserveCycle.lean) · [Path contacts](src/ReserveObstruction.lean) · [Edge opening](src/FlexibleEdge.lean)
* If the misses can be matched to $a,b$, choose any simple path between them in $X$. When there are at least two internal vertices, all internal vertices see $r$. In a nontraceable graph, every pair of clique labels available at successive vertices must agree. This would force just one label along the path, although connectivity of $X$ makes all three cliques meet it. When there is a single internal vertex and neither end touches an unused clique, deleting that vertex and $a,b$ isolates both misses and leaves a third component. The previously checked theorem for adjacent matched misses covers the path of a single edge. [Matched misses](src/MatchedPath.lean) · [Second cut](src/TwinTips.lean)
* If neither miss meets $a$ or $b$, both ends of every spanning path of $G-z$ would have to be the two misses. A rotation making one of them internal contradicts this. When adjacent cubic misses share a port, their external neighbors form a set of at most three whose deletion separates their edge from the edge joining $z$ and $r$. This contradicts the surviving-edge hypothesis. In the other failed-matching cases one can orient the pair so the second miss has two further ordinary contacts. Deleting $x,r,a$ then gives a component joining the second miss $y$ to $b$. A shortest connector leaves a second ordinary contact of $y$ available for opening the cycle. [Rotation](src/Unattached.lean) · [Connector](src/PortConnector.lean) · [Adjacent case without a cubic-independence premise](src/AdjacentShared.lean)
* For nonadjacent misses $x,y$, take an ordinary vertex seeing $x$ alone and one seeing $y$ alone, both adjacent to $r$. These contacts must be adjacent. Otherwise the two contacts, the misses, $r$ and $z$ induce a tree. This supplies the short left path meeting a right path from $y$ to $b$. If both contacts of $x$ lie on the right path, a fresh contact of $y$ reaches the later one and releases the earlier one. The degree argument leaves only two cubic misses with the same single port contact. [Forced adjacencies](src/Exclusive.lean) · [Changing the right path](src/EscapeArm.lean) · [Degree reduction](src/NonadjacentDegree.lean)
* In that cubic case, record the two ordinary neighbors of each miss. Equal pairs give a three-cut isolating both misses. When the pairs differ, they share at most one vertex. Delete $a,r$ and any shared contact. An edge between the two exclusive parts and the edge $bz$ survive. The cut hypothesis supplies an exit from an exclusive contact toward $b$ whose remaining ordinary vertices avoid both pairs. A path through the misses and that exit leaves a neighbor of its first vertex unused, so the three cliques can be joined. [Finding the exit](src/CubicExit.lean) · [Spanning route](src/CubicRoute.lean)

## Provenance and replay

The first 155 Lean files and ordered manifest entries are byte-identical to the frozen single-exception package. Its manifest SHA-256 is `223bb4c214bd46401fc59b95316d44c594f96e3d87e7ae6d82b63cfbb410bb7d`. The proof uses that package’s three-clique obstruction, two-boundary splice, adjacent matched pair, rooted-quartet extension, chordless connectors, three-component deletion theorem, and minimum-counterexample surviving-edge theorem. The new path construction needs no Ore degree-sum bound. The ordered [manifest](Manifest.tsv) supplies the provenance and hash for each Lean module.

Use Lean 4.19.0 and a compiled Mathlib v4.19.0 checkout at commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. From the extracted directory run

```sh
GRAFF199_MATHLIB=/path/to/mathlib4 GRAFF199_LEAN_BIN=/path/to/lean-4.19.0-linux/bin bash replay.sh > StrictReplay.log 2>&1
python3 audit.py
```

The [replay](StrictReplay.log) uses warnings as errors and builds all 177 project modules from source into a fresh temporary directory. The [audit](FinalAudit.log) checks the source digests, exact baseline prefix, compilation order, absence of forbidden proof tokens, and printed axiom dependencies. The graph theorem and the integrated catalogue theorem each use exactly `[propext, Classical.choice, Quot.sound]`.

[Complete pinned Lean sources](proof-sources.tar.gz). Extract the archive and use its replay script.
