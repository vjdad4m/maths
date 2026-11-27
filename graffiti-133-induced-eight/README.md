# Graffiti.pc #133: induced eight-vertex paths without five-cycles

**Partial result for #133.** Lean proves that a finite nonempty graph with no four- or five-cycle and average local independence at least four has an induced path on eight vertices. The proof allows six-cycles. A connected graph in this class with minimum local independence at least three and no such path must have the Heawood structure.

Without five-cycles, the unrounded conjectured bound follows at radius at most three with mean at most five, radius at most two with mean at most six, and radius at most four with mean exactly four. The floor-version bands are radius at most four with floored mean at most four, radius at most three with floored mean at most five, and radius at most two with floored mean at most six.

See [P8NoFive133.lean](src/P8NoFive133.lean), [P8Bands133.lean](src/P8Bands133.lean), and [the remaining-case reductions](src/AfterSeventh133.lean). The general conjecture remains open.

In a Lean and Mathlib 4.19.0 project, run `lake env bash /path/to/maths/graffiti-133-induced-eight/replay.sh`.
