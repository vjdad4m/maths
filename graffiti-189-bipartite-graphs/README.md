# Graffiti.pc #189 for bipartite graphs

Every finite connected bipartite graph satisfies the original #189
claim. Let d be the second-smallest degree (the theorem in fact accepts
any threshold d with at most one vertex of degree below it). If every
vertex has at most d other vertices at even distance, the graph has a
spanning simple path.

In a connected bipartite graph all vertices of the same color are at
even distance. Hence each color class has size at most d+1, and the
whole graph has order at most 2d+2. The checked general order-2d+2 theorem
now applies. There is no lower bound on vertex connectivity or on d.
This is not an unrestricted resolution.

Main theorem:
`Graffiti189LongestPath.BipartiteTraceability.traceable_of_bipartite`.
The bipartition is expressed by a proper Boolean coloring. The file
imports the previously pinned `EJOrderTwoClose189`. Strict Lean 4.19.0
replay with `-j1 -DElab.async=false -DwarningAsError=true` reported only
`propext`, `Classical.choice`, and `Quot.sound`.
