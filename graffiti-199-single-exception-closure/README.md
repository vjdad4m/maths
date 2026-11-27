# Graffiti.pc #199 at connectivity three

In the singleton-cut branch with a spanning path after singleton deletion, a port missing at most one ordinary vertex forces a Hamiltonian path of the original graph. The result holds at arbitrary order. A second theorem covers certain cuts in which every port misses at least two vertices.

## Main theorem

Consider a finite simple graph of exact vertex connectivity three, order at least five and largest induced tree of order at most five. Assume it is nontraceable, its degree-three vertices are independent, and every smaller connected finite graph of order at least two satisfying its own catalogue tree bound is traceable. A separating three-set exists. In every such set, deleting its vertices leaves a singleton $z$ and a connected shore $X$. Write $r,a,b$ for any ordering of the cut. Then

* $r$ misses at least two distinct vertices of $X$.
* If the vertices missed by $r$ are exactly an adjacent pair $x,y$, there is no matching of this pair to $a,b$. Both possible assignments are excluded.
* One path spans the deletion of $z$, and four vertices of that path form an independent set in $X$ such that each cut vertex misses a member. The earlier rooted induced-tree and attachment conclusions remain part of the formal statement.

These conclusions are quantified over every separating triple and all its orderings in `Graffiti199Depleted.Catalogue.Incomplete.catalogue_minimum_misses_and_matching`. The minimum is by vertex count over all graphs satisfying the precise catalogue hypotheses. The proof requires no edge-maximality hypothesis. [FinalCut.lean](src/FinalCut.lean) · [Exact graph invariants and Hamiltonian-walk bridge](src/CatalogueInterface.lean)

## Single exception

Assume connectivity at least three, largest induced tree of order at most five, the singleton-cut structure with a connected ordinary shore, and a spanning path of the graph after deleting $z$. If a port misses at most one vertex of the shore, `SingletonCut.traceable_of_one_almost_complete` gives a Hamiltonian path of the original graph. Minimum order and independence of the cubic vertices are needed upstream to obtain the deletion path. [SingleException.lean](src/SingleException.lean)

1. Under nontraceability, the frozen single-miss result forces a unique miss $x$, with neighbors $a,b$ and a single ordinary vertex $p$. Thus $z,a,x,b$ lie on a four-cycle. Removing the pendant vertex $x$ keeps the ordinary shore connected. [SingleMissCore.lean](src/SingleMissCore.lean) · [PendantExterior.lean](src/PendantExterior.lean)
2. Let $W$ consist of $r$ and the remaining ordinary vertices. The vertex $r$ sees every other vertex of $W$. An independent four-set in the ordinary part, together with $z$, would induce five independent neighbors of $r$ and a six-vertex tree. This proves independence at most three. The exterior is two-connected. [ConeRoute.lean](src/ConeRoute.lean)
3. Collapse the four-cycle to one vertex $d$. The auxiliary graph is three-connected. The package proves for every $k$ that a $k$-connected graph has a spanning path starting at a prescribed vertex $d$ if every independent set avoiding $d$ has size at most $k$. A component omitted by a longest path ending at $d$ gives at least $k$ distinct independent attachment predecessors and one more independent vertex in that component. [TerminalCompression.lean](src/TerminalCompression.lean) · [RootedIndependence.lean](src/RootedIndependence.lean)
4. Start at the contracted vertex. Its first edge selects an actual contact with the four-cycle. Opening the cycle there lifts the spanning path into the original graph. [CompressedRoute.lean](src/CompressedRoute.lean)

## Two or more misses

`SingletonCut.traceable_of_matched_two_misses` assumes the same singleton cut, connectivity and tree bound. If $r$ misses exactly an adjacent pair of ordinary vertices which admit a matching into the other two ports, the whole graph is traceable. This theorem requires neither minimum order nor a Hamiltonian path after deleting $z$. The other two ports can each miss arbitrarily many ordinary vertices. [TwoMissMatching.lean](src/TwoMissMatching.lean)

The matching and the edge between the misses give a cycle through the two misses, the other two ports and $z$. For any nonempty ordinary set $H$ of neighbors of $r$, if the complement of $H\cup\{r\}$ has a spanning cycle, failure of traceability forces $H$ to have exactly three components, each a clique. A missed vertex touching a clique is complete to at least one other clique. When both misses touch the exterior, the path from one miss through the matched ports and $z$ to the other miss can join distinct cliques. When just one miss touches the exterior, minimum degree three forces the other miss to see both of the other ports. That gives enough choices for the endpoint of the path. [NeighborCount.lean](src/NeighborCount.lean) · [ThreeNeighborRoute.lean](src/ThreeNeighborRoute.lean) · [FlexibleExit.lean](src/FlexibleExit.lean) · [BoundaryRoute.lean](src/BoundaryRoute.lean)

An additional criterion applies to any set $M\subseteq X$ containing all vertices missed by $r$. If $X\setminus M$ is connected and $M$ has a spanning path with endpoints contacting $a,b$ respectively, then the graph is traceable. An optional degree-sum certificate fixes both endpoints in an auxiliary supergraph of the induced graph on $M$. For each added edge the sum of the two degrees **in the initial induced graph on $M$** must be at least $|M|+1$. The proof transfers that particular route from the auxiliary graph to the original graph. [MissingPath.lean](src/MissingPath.lean) · [ShoreOre.lean](src/ShoreOre.lean)

The outstanding branch allows each port to miss at least two vertices. A port can miss a nonadjacent pair, an adjacent pair with no matching to the other ports, or at least three vertices. Finding a suitable reserved set and compatible endpoints for every remaining cut is open here. The finite eight-vertex core extension count supplies no hypothesis to these proofs. The full connectivity-three case and unrestricted #199 remain unresolved.

## Provenance and verification

The first 132 source files and their ordered manifest entries reproduce the frozen singleton residual package byte for byte. Its manifest SHA-256 is `60b23973c0940fe1d453147817cae49029211528119498a42b371f4081ce5fc9`. The next 23 files extend that package and include four #189 dependency files. The [manifest](Manifest.tsv) records the ordered transitive source closure and SHA-256 of every file.

The #189 endpoint-preserving theorem in `TerminalOreAdapter199.lean` uses the published theorem signature and proof verbatim, with its private helper imported from `CapEndpoint189`. The latter contains `cap_path_known_end` and `cap_path_forces_end` from `TwoTerminalOre189` and `path_concat_new` from `ArticulationClique189`. The two enumerated Ore files `OreClosure189` and `OreSpliceIndex189` are byte-identical to the degree-four package. [TerminalOreClosure189.lean](https://github.com/vjdad4m/maths/blob/main/graffiti-189-closure-full/TerminalOreClosure189.lean) · [TwoTerminalOre189.lean](https://github.com/vjdad4m/maths/blob/main/graffiti-189-degree-five-cuts/src/TwoTerminalOre189.lean) · [Degree-four sources](https://github.com/vjdad4m/maths/tree/main/graffiti-189-complete-degree-four/src)

From the extracted directory use a compiled Mathlib v4.19.0 checkout at commit `c44e0c8ee63ca166450922a373c7409c5d26b00b` and Lean 4.19.0. Each project module is built from its verified source into a fresh temporary directory with warnings as errors.

```sh
GRAFF199_MATHLIB=/path/to/mathlib4 GRAFF199_LEAN_BIN=/path/to/lean-4.19.0-linux/bin bash replay.sh > StrictReplay.log 2>&1
python3 audit.py
```

The [clean source replay](StrictReplay.log) includes the toolchain versions and the kernel axiom reports. The [audit](FinalAudit.log) checks all 155 source digests and their compilation order, the baseline manifest prefix, forbidden proof tokens, all printed axiom lists, and the exact three standard axioms for the principal results.

[Complete pinned Lean sources](proof-sources.tar.gz). Extract the archive and use its replay script.
