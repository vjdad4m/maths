# Graffiti.pc #189: adjacent singleton cut, order fifteen

This is a partial result for the original conjecture. Under the degree-five hypotheses, for two adjacent deleting vertices with exactly two shores of sizes 1 and 12, there is a spanning path in the original graph. It does not assert the result for larger second-smallest degree.

Main Lean declaration: `Graffiti189LongestPath.CrossSaturation.FiveAdjacent.traceable_of_adjacent_singleton_twelve_shores` in `AdjacentCutFiveFifteenSingletonComplete189.lean`.

The singleton is a common port of degree two, so every other vertex has degree at least five. The six possible distant-color profiles collapse to five with a nonadjacent separator and one balanced profile. In the balanced profile there are at least two common ports. With two, the two common ports join the balanced-even vertex, leaving a seven-vertex Ore path with one endpoint in each strict-even class. With three, the common ports form a clique; the balanced-even vertex can be inserted into the Ore path or used as the final endpoint, unless a nonadjacent separator already exists.

Replay with Lean 4.19, one compiler at a time:
```sh
lean -j1 -DElab.async=false -DwarningAsError=true ...
```

Use the earlier degree-five modules in the same toolchain, especially `AdjacentCutFiveSixteenSingletonGeometry189`, its predecessors, `AdjacentCutFiveMixedNineGeom189`, `AdjacentCutFiveFourteenSingletonTerminal189`, `AdjacentCutFiveFourteenSingletonThree189`, `AdjacentCutFiveFourteenDarkBridge189`, and `DegreeFiveNonadjacentComplete189`. The package manifest pins these new source bytes and the checked transcript.

The last module `ThresholdFiveOrderFifteen189` combines the singleton result with the previous adjacent nonsingleton and global cut reduction. It proves `Graffiti189LongestPath.order_le_fourteen_of_degree_five_counterexample` and the equivalent `traceable_at_degree_five_of_order_ge_fifteen`: at the degree-five threshold, any counterexample has at most 14 vertices. Its external entry points include `AdjacentCutFiveMixedCapFifteen189` and its already checked predecessor modules.

Final replay exits: all declarations in the final two source files were checked strictly, using only `propext`, `Classical.choice`, and `Quot.sound`. The transcript concatenates successful replay sections, not earlier failed diagnostic attempts.

The archive omits the eight explicitly published [frontier modules](../graffiti-189-order-fifteen-singleton-frontier/) listed there; build them and the [order-fifteen cap](../graffiti-189-degree-five-order-fifteen/) first. The order-14 dark-route helper needed by this proof is in this archive. Compile its modules in order.txt order with the pinned earlier objects on LEAN_PATH; the predecessor compatibility overlay for ArticulationClique189 may be needed. See [the global bound](ThresholdFiveOrderFifteen189.lean), [written proof](PAPER-PROOF.md), and [strict staged transcript](LEAN-CHECK.txt).

[Complete pinned Lean sources](proof-sources.zip). Extract the archive and use its replay script.
