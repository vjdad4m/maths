# Graffiti.pc #189: scope of a candidate edge-addition rule

**Later scope correction:** Lean [rules out the exact unique-common degree-five cut configuration](../graffiti-189-unique-exclusion/README.md). The earlier conditional path implication remains valid, but its hypotheses do not occur in this branch.

For nonadjacent cut vertices with exactly one common neighbor, the degree-sum condition in [Easwar and Johari, Lemma 3.3(2)](https://arxiv.org/html/2609.11719v1#S3) is equivalent to there being at most one other vertex adjacent to neither endpoint. This criterion is measured in the original graph.

Under the Graffiti.pc #189 degree-five hypotheses, if the cut vertices are at distance two and removing them leaves exactly two components, that edge-addition test can pass only at order at most 15. In particular this version of the test cannot cover larger graphs. The criterion alone does not give traceability for every graph that passes the test, and the external edge-addition rule is not formalized here. The full conjecture remains open.

`DegreeFiveUniquePortClosureTest189.lean` imports two modules from the [degree-five cuts package](../graffiti-189-degree-five-cuts). The headline theorems are `degree_sum_threshold_iff_at_unique_common` and `order_le_fifteen_of_actual_unique_common_closure_test`. Both use only the standard Lean axioms.

The separate theorem `order_add_left_nonports_le_sixteen_of_five_foreign` in `DegreeFiveFiveForeign189.lean` does not assume that the edge-addition test passes. With exactly five vertices on the opposite component adjacent to at least one cut endpoint, it bounds graph order plus the number of vertices on the common-neighbor component adjacent to neither endpoint by 16. Hence at order 17 and above the opposite side has at most four vertices adjacent to the cut.

There is also a positive route result. In `DegreeFiveUniquePortHighShore189.lean`, `traceable_of_actual_unique_common_test_without_exception` proves a Hamiltonian path when the edge-addition numerical test passes and every vertex off the cut has degree at least five. It uses a direct rooted/terminal Ore argument, not the external edge-addition lemma. The unique vertex allowed lower degree may be a cut endpoint. The case of an off-cut low-degree exception and cuts that fail the test are not covered.
