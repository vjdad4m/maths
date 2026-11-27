# Graffiti.pc #133 when the floored local-independence mean is at most three

The [Lean theorem](src/ThirdBand133.lean) proves the **entire floor-mean-at-most-three case** of the floor interpretation of Graffiti.pc #133, with no radius or cycle restrictions and no regularity assumption. The [original catalogue](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/index.html) prints square brackets around the mean, and this package treats those brackets as floor. It does not settle the unrounded formulation or the higher-mean floor cases.

The central lemma says that a connected four-cycle-free graph with average neighborhood independence at least three contains an induced six-vertex path or has radius at most two. In the absence of five-cycles this follows from the earlier [pruning and induced-path arguments](../graffiti-133-density). For the pentagon case, suppose there is no induced six-vertex path. The pentagon must dominate the graph: otherwise a shortest two-edge attachment to it extends a four-vertex segment of the pentagon. Each outside vertex meets the pentagon in either a singleton or two consecutive vertices.

Local independence at a singleton attachment is at most three, and attaining three uses both opposite singleton types. At most one vertex per singleton type can attain three, and a double attachment has local independence at most two. Summing the local bounds on and off the cycle forces all five singleton types to attain three and rules out double attachments. The incidence constraints then give radius at most two. The Lean proof uses explicit induced paths and local counting, not a census of graphs.

For the floor interpretation, a floor of at most two was already covered. A floor of exactly three needs a six-vertex path only at radius three: the smaller radii follow from the earlier [density release](../graffiti-133-density), and larger radii follow from Chung's general induced-path bound. See that release for both interpretations of the catalogue and references. No priority claim is made.

## Replay

From a Lean 4.19.0 project with the Mathlib 4.19.0 build cache:

    lake env bash /path/to/maths/graffiti-133-floor-three/replay.sh
