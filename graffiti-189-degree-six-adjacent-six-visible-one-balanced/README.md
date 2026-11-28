# Graffiti.pc #189: six visible vertices, one balanced dark vertex

The exact theorem `Graffiti189LongestPath.CrossSaturation.ThresholdSix.traceable_of_adjacent_singleton_thirteen_six_one_balance` produces a spanning path in the original finite simple graph when:

- the graph is connected and all singleton deletions preserve connectedness;
- all but at most one vertex have degree at least six;
- each vertex has at most seven vertices at even shortest-path distance, including itself;
- deleting adjacent cut vertices leaves exactly a singleton and a thirteen-vertex shore;
- exactly six vertices of the large shore see a cut vertex, and exactly one dark vertex is at distance two from both cut vertices.

The cut hypotheses imply order sixteen. This completes the full one-balanced case, not the two-balanced case, the entire degree-six threshold, or the whole conjecture.

## Proof outline

The seven dark vertices split into two strict color classes and one balanced vertex. The old one-exclusive-per-color result handles that shape. Otherwise terminal parity forces precisely three profiles up to swapping terminals. Depending on the balanced vertex's internal degree, use a rooted Ore route on all seven dark vertices or on the other six. A checked 21-bit certificate supplies the compatible exterior path in each profile. Its clauses are derived from graph degree bounds; a clause witnessed by a path is translated into an actual graph walk. A single exceptional visible graph has a direct rooted rotation and path splice.

## Replay

Lean 4.19.0; Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Use the compiled dependencies from the pinned [parent repository snapshot](https://github.com/vjdad4m/maths/tree/18b145e65ca0d5efaf8693a87c4f438f1d56b8a9), then run:

```sh
LEAN_PATH="/absolute/path/to/prior/objects:$LEAN_PATH" ./replay.sh | tee replay.log
```

The direct prerequisite modules are listed in `PRIOR-MODULES.tsv`. Their respective pinned proof packages specify their own transitive imports and replay order. The newest `SixSingletonPositiveProfiles189` is included here and should be supplied before any prior package whose replay imports it. The text-based CNF/LRAT inputs are checked by the proof-term verifier rather than trusted as results of an external solver. No native-decide axiom is used. The final theorem prints only `propext`, `Classical.choice`, `Quot.sound`.
