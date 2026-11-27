# Graffiti.pc #384b: independent ears with small contact counts

At order 33 with 32 nonleaves and 31 distinct triangle-incidence counts, suppose the degree-two vertices are pairwise nonadjacent. Any counterexample to the target 2-domination bound of 17 has at most ten contacts outside the ear and its two neighbors at every ear that is their only common neighbor. [Eleven-contact theorem](src/FinishIndependent.lean)

Moreover, at any contact count, a counterexample must either have a degree-two vertex adjacent to a leaf or two degree-two vertices sharing exactly one neighbor. [Attachment theorem](src/CleanFinish.lean) These alternatives remain open. The proof uses anchor-aware sampling and ranks, not graph enumeration. The nine sources passed strict Lean 4.19 replay with warnings as errors and standard axioms only.

Run `bash replay.sh` with `CROSSFOUR_LEAN_BIN` and `CROSSFOUR_MATHLIB` pointing to Lean 4.19.0 and built pinned Mathlib. It rebuilds the [thirteen-contact baseline](../graffiti-384b-independent13/) and then compiles the hash-pinned sources here in `modules.txt` order.
