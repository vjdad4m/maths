# Graffiti.pc #133: four attachment points and mean local independence

These are partial results about a connected dominating core with no induced seven-vertex path in a graph with no four-cycle. The four designated core vertices contain every endpoint of an edge from outside the core.

- The ambient average local independence is at most four if at least two edges occur among the four attachment points. The proof splits between two incident edges and two disjoint edges. Arbitrary multiple attachments are allowed; this part does not assume absence of an induced nine-vertex path.
- For four independent attachment points sharing a core neighbor, the absence of an induced nine-vertex path bounds the number of exterior vertices with local independence four by six per attachment point. If the core has at least 24 units of slack relative to the mean-four bound, this proves the same ambient bound.
- An independent exchange argument gives the mean-four bound with unique exterior attachments when a minimum core admits the stated two erasable singleton-client attachment points.
- A checked 12-vertex example shows that an induced-nine-path-free ambient graph can still have an exterior vertex of local independence four when the four attachment points are independent. This does not violate the mean-four bound or refute #133; the displayed core is not minimum.

The sparse cases outside these hypotheses and the full conjecture remain open. The new modules passed strict Lean 4.19.0 replay with standard axioms only. With pinned Mathlib and the objects for [CambyDomBase133](../graffiti-133-full-four/src/CambyDomBase133.lean) and [HexFlattened133](../graffiti-133-induced-seven/src/HexFlattened133.lean) on the Lean search path, compile the source modules in `modules.txt` order.
