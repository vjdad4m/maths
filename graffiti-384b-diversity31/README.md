# Graffiti.pc #384b: the 31-count frontier

**Partial result.** For every connected finite simple graph with exactly 31 distinct vertex triangle counts, the conjecture holds provided the graph contains no (K_5) with one edge removed as a (not necessarily induced) subgraph. More precisely, any counterexample at diversity 31 must contain five vertices spanning at least nine edges, including a vertex of degree between four and nine. [Exact Lean theorem](Frontier31Finish.lean)

A second theorem narrows the remaining cases according to the number of nonleaves. If there are 30, one can keep the same triangle counts in a connected induced graph of order 31 whose 30-vertex positive core has 2-domination number exactly 15. If there are 31 nonleaves, there must be a degree-five-through-eight vertex on a five-clique with more than (lfloor d^2/3
floor) triangles through it. With 32 nonleaves two such vertices of different degrees are required. [Case split](Diversity31Frontier.lean)

The unrestricted conjecture is not settled. The earlier [diversity-33 development](../graffiti-384b-diversity33/) proves the inequality whenever at least 32 distinct counts occur.

[Strict compiler transcript](Strict226.log) records the audit of all 226 source modules and 527 standard-axiom reports. The nine new modules are pinned by `NEW-SOURCES.sha256`. To rebuild the public dependency cone, use the same Lean/Mathlib v4.19.0 environment and `CROSSFOUR_LEAN_BIN` and `CROSSFOUR_MATHLIB` settings as the prior package, and run `bash replay.sh`.
