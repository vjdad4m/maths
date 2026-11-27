# Graffiti.pc #133: four attachment points with one edge

Let a connected dominating induced core contain no induced seven-vertex path. Suppose that all edges to the exterior meet one of four designated core vertices, those four vertices have exactly one edge among them, and the ambient graph has no four-cycle or induced nine-vertex path. Lean proves that the ambient average local independence is at most four, allowing arbitrary exterior attachments and arbitrary core size.

Three full-score fans at the same isolated attachment point would force a forbidden induced nine-vertex path or a four-cycle. Thus at most two such fans occur at either isolated attachment point, and at most one further full-score exterior vertex can have multiple attachments. If all six pairs of attachment points are used by the multiple attachments, a triangle containing the unique edge gives a one-unit discount, so the available core slack suffices.

[Main theorem](src/P5CliqueSingleEdgeMultiClosure133.lean) · [Three-fan obstruction](src/P5CliqueSingleEdgeTripleFan133.lean) · [Crossing discount](src/P5CliqueSingleEdgeCrossDiscount133.lean)

Together with the [case of at least two edges](../graffiti-133-four-palette/), this handles every four-point palette containing an edge in the stated scope. The independent palette and the full conjecture remain open. Compile in `modules.txt` order with pinned Lean 4.19 and the [sparse-palette package](../graffiti-133-sparse-palette/) objects on the Lean search path. The proofs passed a strict replay with only standard axioms.
