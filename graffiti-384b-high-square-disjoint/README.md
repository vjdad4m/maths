# Graffiti.pc #384b at 29 triangle-count types and 28 nonleaves

**A surviving five-clique-free core must have two external cubic vertices with disjoint neighborhoods.** Let $G$ be a finite simple graph with 29 distinct vertex triangle counts and 28 vertices of degree at least two. Induce on those 28 vertices and retain every edge belonging to a triangle. Write $J$ for the resulting graph. If $G$ violates the catalogue bound and $J$ has no five-clique, the previous release forces a degree-two vertex $e$ with adjacent neighbors $a,b$, and an additional common neighbor $s$ of $a,b$. In this report every local degree, adjacency and triangle count refers to $J$. [Core definitions and previous reduction](https://github.com/vjdad4m/maths/tree/3dc8b1b8c035681d79346b34dffd705ff932673f/graffiti-384b-thin-quartic-core)

Both $a$ and $b$ have degree at least four. Every choice of $s$ has degree at least five and lies in at least four triangles. There is an induced five-clique minus an edge, disjoint from $\{e,a,b\}$. Outside both sets are a cubic $u$ of triangle count two and a cubic $v$ of triangle count three. They are nonadjacent, and their neighbor triples are disjoint. The bound on the original graph follows in every subcase this excludes. [Original-graph theorem](HighDisjoint28.lean)

## Three repair counts

The core of a hypothetical failure has positive, pairwise distinct triangle counts and 2-domination number at least 14. Each row gives the total repair mass over its specified choices. Strict inequality produces a 2-dominating set of at most 13 vertices in the core.

| Configuration | Choices | Upper bound | Required for failure | Margin |
|---|---|---:|---:|---:|
| Cubic endpoint $a$ | Keep $\{e,s\}$ or $\{a,b\}$ and choose nine of 24 | 7,320,924 | 7,845,024 | 524,100 |
| Unique fourth $s$, unique cubic outside the ear triangle, endpoints of degree at least four | Keep $a,b$ plus eight of 25 with weight three, or $e$ plus ten of 25 with weight one | 22,767,167 | 22,785,180 | 18,013 |
| Cubics $u,v$ with exactly one common neighbor | Retain their common neighbor and one private neighbor of each cubic, then choose eight of 21 | 2,433,041 | 2,441,880 | 8,839 |

For the first row, the neighborhood of the cubic endpoint is exactly $\{e,b,s\}$. No exterior vertex sees $e$ or that endpoint, so each receives at most one fixed neighbor in either trial. The 24 exterior ranks start at triangle count three. [Cubic endpoint](HighEndpoint28.lean)

For the second row, a unique fourth gives each endpoint with $d$ exterior neighbors at most $2+\binom{d}{2}$ triangles. At most one endpoint has just two exterior neighbors, since the ear and the exterior cubic already use two of the counts from one through three. The two endpoint credits therefore total at least 3,035,850. In the previous single-cubic fan alternative, a cubic tip of the fan would share two central neighbors with the external cubic. The earlier shared-neighbor exclusion rules this out. All three fan centers have degree at least four, so the unique-exterior-cubic estimate applies. [Coupled trials](SingleFinish28.lean) · [Fan and endpoint reductions](HighFrontier28.lean)

For the third row there are four choices of private neighbors. Both cubics and the unused private neighbor on the score-three side are already protected. The unused private neighbor on the other side may need repair and is included in the count. With two or more shared neighbors the frozen `CorePair28.shared_saving` theorem applies because the five-clique transversal condition holds vacuously. Adjacency of the two cubics would itself force at least two common neighbors. [Four-choice estimate](PortSaving28.lean) · [All shared-neighbor cases](HighDisjoint28.lean)

## Two protected cuts in the disjoint case

For each fourth vertex $s$ missing both cubics, form $K=(N(s)\cap N(v))\setminus\{a,b\}$, with $v$ the score-three cubic. **If $K$ has at least two vertices, at least one ear endpoint has no neighbor in $K$.** The theorem also covers a single fourth vertex on the square. [Original-graph contact restriction](OddSquare28.lean)

Indeed, if both endpoints touch $K$, choose two members $Q$ of $K$ together touching both. The closed neighborhood $C$ of $v$ is a four-clique. Pin $(C\setminus Q)\cup\{a,b\}$ on one side and $Q\cup\{e\}$ on the other. All pins see two opposite pins, and $s$ sees two pins on each side. Isolating $s$ leaves every free vertex of degree at least three, since the remaining potentially vulnerable cubic $u$ misses $s$. A maximum cut respecting the pins gives two 2-dominating sets partitioning the 27 vertices other than $s$. One has at most 13 vertices. The core-level theorem also allows $u$ to be pinned when it already sees two fixed neighbors on one side. [Cut and pinning proofs](OddSquare28.lean)

There is a second restriction when $s$ touches one of the two cubics, say $h$. Write $r,t$ for the other two neighbors of $h$ and assume that both see $s$ and are distinct from $a,b$. There can be no matching of the two ear endpoints to $r,t$. For the score-three cubic, the condition that $r,t$ see $s$ is automatic. For the score-two cubic it holds when $s$ is the middle vertex of its three-vertex neighborhood path. [Matching exclusion](MatchedSquare28.lean)

A proposed matching $a$–$r$, $b$–$t$ would protect the sides $\{h,a,b\}$ and $\{e,r,t\}$. The fourth vertex $s$ receives two pins on each side. Disjoint cubic neighborhoods ensure that the other cubic misses $s$. Isolating $s$ again leaves 27 vertices to partition, giving a core 2-dominating set of size at most 13. The proof allows either pairing by interchanging $r,t$. [Original-graph score-three specialization](MatchedSquare28.lean)

The disjoint-cubic case remains open when these contact restrictions hold. Preliminary optimization did not supply a universal repair discount there. The certificate uses finite degree and rank inequalities with Lean-verified graph coverage. It does not enumerate all cores or exhibit a counterexample. The branch containing a five-clique and other diversity or nonleaf counts are outside this release.

## Source map and replay

| New files | Purpose |
|---|---|
| `HighTable28`, `HighBasics28`, `HighTrial28`, `HighEndpoint28` | Finite tables, sample bounds, two-sided square sampler and the endpoint exclusion |
| `SinglePrice28`, `SingleFinish28`, `HighFrontier28` | Endpoint contact credits, single-cubic exclusion and the forced pair |
| `PortFibers28`, `PortGeometry28`, `PortBudget28`, `PortRepair28`, `PortSaving28` | Four choices, rank coverage, completion, counting and one-common-neighbor exclusion |
| `HighDisjoint28`, `OddSquare28`, `MatchedSquare28` | Original-graph conclusions and the two protected cuts |

The port calculation adapts the earlier 30-vertex `CommonGeometry31`, `CommonBudget31`, `CommonRepair31` and `CommonSaving31` sources and the eight-subset counting argument from `SevenFibers`. Their numerical conclusions have different orders and pool sizes. The new proofs change the pool to 21, use the five-clique-free neighborhood bound and recompute every rank inequality. The protected cut reuses `CliquePivot33.shared`. [Earlier common-neighbor sources](https://github.com/vjdad4m/maths/tree/main/graffiti-384b-thirty-closure) · [Earlier fiber proof](https://github.com/vjdad4m/maths/blob/main/graffiti-384b-ear-cubic31/SevenFibers.lean)

The replay pins Lean 4.19.0 commit `6caaee842e94` and Mathlib v4.19.0 commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Set `CROSSFOUR_LEAN_BIN` and `CROSSFOUR_MATHLIB` for a standalone extraction. Checked mode expects the workspace containing the object paths in the ledger. Cold mode rebuilds all 288 predecessor modules from the recursively bundled, hash-checked sources.

```sh
python3 replay.py --cold
python3 replay.py --checked /absolute/path/to/shared/workspace
```

Both recorded executions used checked mode, freshly compiled all 15 new modules with warnings as errors and compared every resulting object with its recorded digest. All 30 axiom reports list only standard axioms. [Replay entry point](replay.py) · [First replay](StrictHighSquare.first.log) · [Second replay](StrictHighSquare.log) · [Fresh sources](NEW-SOURCES.sha256) · [Fresh objects](NEW-OBJECTS.sha256) · [Predecessor sources](PRIOR-SOURCES.sha256) · [Predecessor objects](CHECKED-OBJECTS.tsv)
