# Graffiti.pc #180: bipartite and low-eccentricity cases

**Partial result.** Lean proves the #180 inequality for nontrivial connected bipartite graphs, for graphs where some vertex attaining the maximum even-distance count has eccentricity at most three, and when the minimum number of vertices whose deletion makes the graph bipartite is at most the second-smallest degree.

See [Proof180.lean](src/Proof180.lean), specifically `bipartite180`, `result180`, and `small_transversal`. The general conjecture remains open. The copied prerequisites are the exact source versions used for this verification.

In a Lean and Mathlib 4.19.0 project, run `lake env bash /path/to/maths/graffiti-180-partial/replay.sh`.
