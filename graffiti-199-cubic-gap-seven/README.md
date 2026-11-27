# Graffiti.pc #199 total gap seven

## Exact scope

Let G be a finite simple graph with induced-tree number at most five. Suppose a path spans G minus a cubic vertex z. The three neighbors of z are independent, and at least one is cubic. The two gaps between consecutive visits to those neighbors are measured in edges.

- Placement25.lean proves Graffiti199Depleted.WiderOmission.traceable_of_gaps_two_five and traceable_of_gaps_five_two.
- Placement34.lean proves Graffiti199Depleted.WiderOmission.traceable_of_gaps_three_four and traceable_of_gaps_four_three.
- GapSevenBound.lean proves Graffiti199Depleted.WiderOmission.sum_intervening_at_least_six. In a nontraceable graph the two gaps have at least six intervening vertices combined, or at least eight edges.
- GapSevenBound.lean also proves Graffiti199Depleted.ContractedEdge.minimum_cubic_edge_total_gap_eight for every path with the omission furnished by the archived cubic-edge contraction. Its extra premises are the smaller-order hypothesis, connectivity at least three, the surviving-edge crossing condition, and the archived order bound.

The next pairs in this branch have total gap eight. The argument leaves open a classification of all larger placements and the general conjecture.

## Transfer reusable at larger orders

UniformProfiles.lean proves Graffiti199Depleted.WiderOmission.twins_of_uniform_flank. When an induced core chart has an adjacent pair with equal internal contacts, and its checked single-exterior profiles give equal contacts to the pair, they are adjacent true twins throughout the graph. The two residual 2-and-5 rows contain induced copies of the published 2-and-3 and 2-and-4 charts. The twin detection uses these smaller charts. Deleting a twin in the long gap preserves both cubic degrees and the tree bound, after which the published 2-and-4 theorem applies. The route in that graph expands by reinserting the deleted twin.

TwinMinimum.lean proves Graffiti199Depleted.AdjacentTwins.traceable_of_minimum. In the archived cut case, when all common neighbors of adjacent twins have degree at least four, deleting one twin preserves three-connectivity. This gives a smaller instance to which the minimum-order hypothesis applies.

ChartMinimum.lean combines the latter theorem with the smaller checked charts. Graffiti199Depleted.WiderOmission.traceable_of_minimum_23_chart and traceable_of_minimum_24_chart exclude the specified induced charts, with their two named cubic degrees, anywhere in a minimum-order counterexample satisfying the archived connectivity and crossing hypotheses. Both proofs apply to graphs of arbitrary order. An arbitrary longer gap placement still needs to be shown to contain one of these charts or admit a different splice.

The local classifications reuse the finite clause engine and graph transfers from [gap six](https://github.com/vjdad4m/maths/tree/main/graffiti-199-cubic-gap-six). The 3-and-4 rows use core replacement routes. FullMaskCover.lean certifies that every adjacency bit is known at a residual leaf in one mask comparison, which avoids revisiting each core pair at every such leaf.

## Strict replay and provenance

The toolchain is Lean 4.19.0 and Mathlib revision c44e0c8ee63ca166450922a373c7409c5d26b00b. SourceManifest.tsv lists the ordered new modules. PublishedSources.tsv lists the ordered public dependency closure, with SHA-256 source hashes. PublicBlobAudit.tsv records the corresponding GitHub main blob hashes. StrictReplay.log records warnings-as-errors verification and the scope theorems' standard axioms.

From the repository root, set `GRAFF199_MATHLIB` to the pinned, built Mathlib checkout and optionally `GRAFF199_LEAN_BIN` to the toolchain's bin directory. Then run:

~~~sh
bash graffiti-199-cubic-gap-seven/replay.sh --from-source "$PWD"
~~~
