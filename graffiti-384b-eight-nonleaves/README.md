# Graffiti.pc #384b: the eight-nonleaf case at diversity nine

For every finite simple graph with **exactly eight vertices of degree at least two** and at least nine distinct vertex triangle counts, the catalogue two-domination inequality holds. Connectivity is not required. Zero is counted when it occurs. In the hypotheses, nine is the only possible diversity. This does not settle the more general conjecture, or the nine-to-twelve-nonleaf cases of diversity nine or ten.

Main theorem: `Graffiti384b.Q8.exact_of_eight_nonleaves` in [Q8Exact384b.lean](src/Q8Exact384b.lean).

## Proof

1. Every triangle is contained in the nonleaf core. Since all other vertices have triangle count zero, diversity at least nine forces the eight core vertices to have positive, pairwise distinct counts.
2. In a graph on eight vertices satisfying that condition, the top two triangle counts are at least seven. Their vertices both have degree at least five. If they have five common neighbors, those neighbors can all be omitted from a two-dominating set.
3. Otherwise there are eight possible contact profiles for the two top-count vertices. Relabeling the six remaining vertices by which anchors they see fixes every edge incident to either anchor and leaves fifteen free edges. A checked finite decision tree covers all their assignments in each profile. Each leaf either contradicts positivity, distinctness or the two-anchor rank condition, or provides an explicit retained triple. In a triple witness, every omitted vertex already has two neighbors along forced edges, so it works in the actual graph.
4. The model counts equal the graph's triangle counts. The checked triple lifts to a two-dominating set for the original graph by retaining all noncore vertices.

The decision trees are in the eight Q8Shape modules. Lean checks their Boolean conditions and proves every checked tree gives an actual graph witness. The proof does not execute an external solver at replay. The separate t=9/10 SAT experiments do not enter this package.

## Replay

Use Lean 4.19.0 (6caaee842e94) and Mathlib v4.19.0 (c44e0c8ee63ca166450922a373c7409c5d26b00b). Build the [baseline partial](../graffiti-384b-partial/) and [diversity-29](../graffiti-384b-diversity29/) packages, retaining their objects and transitive dependencies on LEAN_PATH. Then run `lake env bash /path/to/this/package/replay.sh`. All fourteen modules are built with synchronous elaboration and warnings as errors; the recorded audits use only propext, Classical.choice, and Quot.sound. See [source hashes](sources.sha256) and [strict logs](StrictReplay.log).
