# Graffiti.pc #189: degree-five distance-two (1,4) two-shore case

Exact conclusion: an original-graph spanning path. Hypotheses: finite connected simple graph; cut pair a,b at distance two; connected after every single deletion; distinct actual cut components C,D whose shores cover all off-cut vertices; exactly one total cut port in C and exactly four in D; each even-distance set including its center has at most six elements; every distinct pair has at least one vertex of degree at least five. No common-porter assumption on either shore.

Sources in module order:
- DegreeFiveOneFourShapes189.lean a439f86ff9581c0c37daf8aa0c6633b8db355194402d063b0ce83d0ce1c1e0b0
- DegreeFiveOneFourClose189.lean 6d21a646a9185eb1463eb6b368b435f0ae1696afe7d5fd50b2c5101278cbecfc

Dependencies: the [2+4 release](../graffiti-189-two-four-shores) (shared geometry and rooted small shores) and the [2+5 and 3+5 release](../graffiti-189-two-three-five-shores) (nonport-neighbor fact), subsequent actual-cut and mathlib overlays, WingSignature189, UniversalRouteSingletons189, rooted Ore. New modules retain exact public import and private-open sections. Serial Lean 4.19.0/mathlib 4.19.0 flags: -j1 -s 65536 -DElab.async=false -DwarningAsError=true, using the same dependency overlay as the public package.

Combined source replay exited successfully. Graffiti189LongestPath.CrossSaturation.FiveActualCut.one_four_shore_shape, free_all_high_four_port_shore_at_most_eight, and traceable_of_actual_five_one_four_ports printed exactly [propext, Classical.choice, Quot.sound]. The final correction is the inverse union_insert rewrite, included in the frozen hash. No `sorry`, `native_decide`, or graph enumeration.

Single deletion forces the one-port shore to be a singleton touching both cuts; both cuts must then be high, so every port of D is shared. Four-foreign saturation restricts D to order≤8 and all high. For D7/8, complete only missing pairs incident to its nonporters, using valid rooted Ore sums. The filled nonporters act as universal separators among the four ports; pull back the port-rooted path and splice through the singleton. This stage does not assert (1,5).
