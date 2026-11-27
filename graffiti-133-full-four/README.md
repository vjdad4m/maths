# Graffiti.pc #133: the full mean-four range

**Partial result for the conjecture.** Lean proves the unrounded formulation whenever average local independence is at most four. It also proves the catalogue's floored formulation whenever the floor of that average is at most four. Both theorems cover every radius and allow five-cycles.

The main new ingredient is that a finite connected graph without an ordinary four-cycle, of average local independence at least three, either contains an induced eight-vertex path or has radius at most three. At radius at least four, a connected dominating subgraph with no induced six-vertex path reduces to a dominating induced hexagon, while the other possibility is a dominating induced octagon. The hexagon argument gives a strict bound below mean three without an induced eight-vertex path, and the octagon either spans the graph or supplies a center at distance at most three from every vertex.

The dominating-subgraph decomposition is a Lean formalization of [Camby and Schaudt's characterization of induced-path-free graphs](https://arxiv.org/abs/1402.7213), specialized to the cases used here. The [main structural theorem](src/FinalEight133.lean) and [both final wrappers](src/FirstBandFour133.lean) replay with only the usual Lean axioms. This does not settle larger averages in general.

From a Lean and Mathlib 4.19.0 project, run `lake env bash /path/to/maths/graffiti-133-full-four/replay.sh`.
