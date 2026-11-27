# Graffiti.pc #384b: the full leaf-adjacent independent case

Let the graph have 33 vertices, 32 nonleaves, and 31 distinct vertex triangle-incidence counts. If the degree-two vertices are pairwise nonadjacent and any touches a leaf, Lean proves that a 2-dominating set of size at most 17 exists. No anchor-contact count restriction is required. Other degree-two vertices may share neighbors. [Catalogue theorem](src/LeafFinish.lean)

The proof also gives an exact deletion rule: if a leaf l has neighbor e with precisely two neighbors l and b, deleting l and e lowers the optimum by exactly one when the remaining 2-dominating set is required to contain b. [Exact rule](src/LeafDeletion.lean)

In the 33-vertex reduction, the [previous independent results](../graffiti-384b-independent-small/) and this package leave the case in which all degree-two vertices have high-degree neighbors, two degree-two vertices share exactly one neighbor, and every thin ear has at most 10 contacts. Full #384b remains open.

The new sources passed strict Lean 4.19 replay over the frozen 270-module baseline, with standard axioms only. Run `bash replay.sh` with `CROSSFOUR_LEAN_BIN` and `CROSSFOUR_MATHLIB` pointing to Lean 4.19.0 and built pinned Mathlib. The script rebuilds the thirteen-contact baseline, the prior independent modules and these three modules, checking exact source hashes.
