# Graffiti.pc #384b: every five-clique-free graph at diversity 31

**Partial result.** If a finite connected simple graph has exactly 31 distinct triangle-incidence counts and contains no five-vertex clique, then its 2-domination number is at most its order minus 16. Lean also proves that a counterexample at diversity 31 would have a connected induced counterexample on at most 33 vertices preserving exactly the triangle-count palette and itself containing a five-vertex clique. [Final theorems](CreditFinish31.lean)

In the 30-vertex positive core, a first sample forces the degree sum of the two ear neighbors to be at least 16. A second sample retains both neighbors and handles all the common-neighbor cases using the degree-four pivot. Each of those cases yields a 2-dominating set of size at most 14, contradicting the required 15. No cubic-transversal premise is needed. The five-clique branch at diversity 31 and the general conjecture remain open.

Replay using the same pinned Lean/Mathlib 4.19.0 and `CROSSFOUR_LEAN_BIN` and `CROSSFOUR_MATHLIB` settings as the [adjacent ear–cubic package](../graffiti-384b-ear-cubic31/). Run `bash replay.sh`. [Strict compiler transcript](Strict241.log)
