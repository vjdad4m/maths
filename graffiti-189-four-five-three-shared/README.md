# Graffiti.pc #189: 4+5 cut with three shared contacts

Under the degree-five hypotheses and single-deletion connectivity, consider a distance-two cut leaving two components with four and five attachments, respectively. If the four-attachment side has at least three common neighbors of the two cut vertices, and the five-attachment side has at least one, Lean constructs compatible paths on the two sides at every order. The published wing-splice theorem turns those paths into a Hamiltonian path of the original graph. [Complementary paths](src/DegreeFiveFourFiveThreeShared189.lean) · [Wing splice](../graffiti-189-both-five-shores/src/WingSignature189.lean)

No edge is added to the original graph. The cases with one or two shared contacts on the four-attachment side are outside this theorem.

Build the [order-fifteen 4+5 package](../graffiti-189-four-five-order-fifteen/) with its documented dependencies. Use Lean 4.19.0 and Mathlib 4.19.0 at commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. With predecessor objects on the Lean search path, check `sha256sum -c sources.sha256` and compile the three modules in `modules.txt` order with warnings as errors and asynchronous elaboration disabled. Strict replay reported only `propext`, `Classical.choice`, and `Quot.sound`.
