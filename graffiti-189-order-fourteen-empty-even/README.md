# Graffiti.pc #189: order fourteen, singleton adjacent shore, multi-exclusive with empty equal-even class

This is an exact exclusion of three profiles in the degree-five threshold case. The hypotheses are those of two adjacent cut vertices with exactly two shores (the first a singleton); all vertices have at most six even-distance vertices including themselves, vertex deletions of size less than two preserve connectivity, and at most one vertex has degree below five.

For the opposite shore, define endpoint-distance index in the order:
strictly nearer the left cut vertex at even distance, strictly nearer the right at even distance, same even distance, strictly nearer left at odd distance, strictly nearer right at odd distance, same odd distance. The result excludes precisely the possible profiles
`(2,4,0,1,2,2)`, `(3,3,0,1,2,2)`, and `(3,3,0,2,2,1)`
up to reversing the cut vertices. This alone does not cover other order-fourteen profiles, let alone the full conjecture.

All odd vertices here are literal cut ports and each strict-even vertex has depth two. The singleton and missed ports repeatedly use up allowable positive-even-distance slots; the profile cases then contradict the degree-five condition or the even-distance cap.

Main module: `AdjacentCutFiveFourteenMultiComplete189.lean`, declaration `Graffiti189LongestPath.CrossSaturation.FiveAdjacent.impossible_actual_adjacent_singleton_multi_empty_even_fourteen`.

External checked prerequisites include the existing singleton order-fifteen modules and `AdjacentCutFiveFourteenSingletonTerminal189`. Replay new sources with Lean 4.19.0, `-j1 -DElab.async=false -DwarningAsError=true`.

See the [final Lean theorem](AdjacentCutFiveFourteenMultiComplete189.lean), [strict verification](LEAN-CHECK.txt), and the archive's module list in order.txt. It builds on the [order-14 frontier](../graffiti-189-order-fourteen-singleton-frontier/) and [order-15 singleton geometry](../graffiti-189-degree-five-order-fourteen/).

[Complete pinned Lean sources](proof-sources.zip). Extract the archive and use its replay script.
