# Graffiti.pc #189: the full degree-four case

**Lean proves the whole degree-four case.** Let (G) be a finite, simple, connected graph whose second-smallest degree is four. If from every vertex at most five vertices are at even shortest-path distance, counting the vertex itself, then (G) has a Hamiltonian path. There is no restriction on order or vertex connectivity. In Lean the degree hypothesis is written as: at most one vertex has degree below four. [Final theorem](src/DegreeFour189.lean)

The [previous proof](../graffiti-189-cross-saturation/) covers the 2-connected case. Here the parity count at a cut vertex forces exactly two sides, each of size at most eight. Rooted Ore closure builds a spanning path from the cut on each side, and concatenating those paths gives the required Hamiltonian path. The rooted closure argument adds a leaf to force the chosen endpoint and then uses a universal vertex to reduce ordinary path closure to cycle closure. See [the closure theorem](src/OreClosure189.lean).

The articulation case was already proved mathematically at general degree by [Easwar and Johari, Theorem 5.11](https://arxiv.org/html/2609.11719v1). This is an independent Lean formalization of that branch at degree four, not a novelty claim for articulation. The unrestricted-degree Graffiti.pc #189 is not settled here.

## Replay

In a prepared Mathlib v4.19.0 checkout, run `lake env bash /path/to/maths/graffiti-189-complete-degree-four/replay.sh`. The script rebuilds the earlier public dependency cone, verifies all new source hashes, and checks the final axiom report. [Strict modular transcript](StrictReplay.log).
