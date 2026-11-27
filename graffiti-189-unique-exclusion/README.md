# Graffiti.pc #189: no unique-common distance-two two-component cut at degree five

Under the degree-five #189 hypotheses, deleting two vertices at distance two cannot leave exactly two components if the two cut vertices have exactly one common neighbor. This exclusion does not assume the numerical edge-addition test. It supersedes the bound in the earlier [eligible-cut package](../graffiti-189-closure-full/README.md): its path theorem remains valid, but its exact degree-five cut hypotheses do not occur.

[Main theorem](DegreeFiveNoUniqueCommon189.lean): `FiveActualCut.no_unique_common_at_actual_five_distance_two`. The proof uses a separate [exclusion of up to three opposite contacts](DegreeFiveThreeForeignImpossible189.lean) and refines the four- and five-contact geometry. Both modules passed a strict Lean 4.19 replay and use only standard axioms. This is not a solution of the full conjecture. Cuts with more than one common neighbor require different arguments.

With pinned Mathlib and prior modules on the Lean search path, compile `DegreeFiveThreeForeignImpossible189.lean` and then `DegreeFiveNoUniqueCommon189.lean`. The public prerequisites are the [degree-five cuts](../graffiti-189-degree-five-cuts/), [additional cuts](../graffiti-189-degree-five-more-cuts/), [closure-test](../graffiti-189-closure-test/), and [full numerical test](../graffiti-189-closure-full/) packages.
