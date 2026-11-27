# Graffiti.pc #384b: the full adjacent degree-two case

For a finite simple graph of order 33 with 32 vertices of degree at least two and 31 distinct vertex triangle-incidence counts, Lean proves that two adjacent degree-two vertices imply a 2-dominating set of size at most 17. There is no restriction on the number of anchor contacts or on connectivity. [Full theorem](src/CompleteAdjacent.lean)

The proof keeps the neighbors needed to omit the third degree-two vertex and one endpoint of the adjacent pair. It ranks the triangle counts of three fixed high-degree vertices together with the sample pool and counts further safe removals of sampled vertices whose neighborhoods are cliques. The two final modules passed strict Lean 4.19 replay against hash-checked objects for the exact earlier modules included here. Only the standard axioms occur.

This settles the adjacent case at these quotas, not the full conjecture. Run `bash replay.sh` with `CROSSFOUR_LEAN_BIN` and `CROSSFOUR_MATHLIB` pointing to Lean 4.19.0 and built pinned Mathlib. It rebuilds the [pendant baseline](../graffiti-384b-pendant16/), then compiles the present files in `modules.txt` order, checking all source hashes.
