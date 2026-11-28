# Graffiti.pc #189 for split graphs

Every finite connected split graph with actual second-smallest degree (d\ge2)
satisfies #189: if each vertex has at most (d) other vertices at even
distance, the graph has a spanning simple path. A split graph is a graph
whose vertex set partitions into a clique and an independent set. No lower
bound on vertex connectivity or orders is needed. This does not resolve
#189 for general graphs.

For an independent-side vertex (u), all missed clique vertices and all
other independent-side vertices sharing a clique neighbor with (u)
consume one unit each of the distance-two budget. Use this budget with
the actual second degree to bound the independent side. Complete or nearly
complete clique attachments handle the small clique cases, including one
exact longest-path order check. The generic insertion lemma gives a path
starting at any chosen clique vertex when each independent vertex has at
least one more clique neighbor than there are independent vertices remaining.
The possible low vertex is prepended at its clique neighbor. The proof
uses the already checked articulation result where necessary.

Main theorem: `Graffiti189LongestPath.SplitTraceability.traceable_of_split`.
Strict replay: Lean 4.19.0, `-j1 -DElab.async=false -DwarningAsError=true`;
imports `SmallSeparator189`, `ArticulationGeneralClosure189`, and
`ThreeFifthsDeficit189` through the pinned #189 modules. The only reported
axioms are `propext`, `Classical.choice`, and `Quot.sound`.

With the pinned dependency objects on LEAN_PATH, run `lean -j1 -DElab.async=false -DwarningAsError=true SplitTraceabilityCombined189.lean`. See the [audit](VERIFIED.log).
