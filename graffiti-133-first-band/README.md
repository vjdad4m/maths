# Graffiti.pc #133: endpoint restrictions in the first unresolved real band

**Partial result.** In the unrounded formulation, every counterexample with mean local independence at most four has radius four and mean strictly above three. Lean proves two further restrictions:

* For any pair of vertices at distance at least five, at least one endpoint has local independence at most one. At distance at least six, both endpoints do. The supporting geodesic-extension lemmas need local lower bounds only near the path endpoints.
* If the minimum local independence is at least two, the diameter is four. If there are also no five-cycles, the mean is strictly less than four, and every endpoint of every induced seven-vertex path has local independence at most two.

See [the endpoint constraints](src/GeoEndpointBands133.lean) and [the diameter-four reduction](src/AfterEighth133.lean). None of these statements resolves the full conjecture.

In a Lean and Mathlib 4.19.0 project, run `lake env bash /path/to/maths/graffiti-133-first-band/replay.sh`.
