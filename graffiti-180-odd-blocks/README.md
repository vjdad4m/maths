# Graffiti.pc #180: odd blocks in the tight triangle transition

Write $G=J+xy$ with $xy$ absent from the connected lower graph $J$, and let $w$ be a common lower neighbor of $x,y$. In the catalogue reduction, $G$ has no cut vertex, is rooted-sparse at $r$, and $d_G(x,r)=d_G(y,r)$. The chord costs one vertex of bipartite order. Lower tightness for the chosen independent set $A$, distance-parity set $P$, and eligibility set $U$ means $\ell_J(U)+b(J)=1+|A|+|P|$. Here $\ell$ maximizes the number of eligible leaves in a spanning tree. A first-form certificate has $\ell_J(U)+1$ eligible vertices and keeps both chord tips in the connected upper core. A second-form certificate uses one tip as a leaf and requires the chord for that tip's domination.

## What the proofs establish

* In a rooted-sparse block, every connected induced bipartite piece whose only possible contacts with the exterior are two adjacent vertices consists of those two vertices. The proof starts from a rank-preserving recoloring. Deleting internal edges of such a bipartite piece preserves bipartite order whenever its two ports still communicate inside it. For an edge on an internal cycle this contradicts rooted sparsity, which puts all rank-preserving edges in a single tree. The piece inherits absence of cut vertices by projecting the exterior to a surviving port.
* For order at least four the lower graph is nonbipartite. If it has a cut, its only possible cut vertex is $w$. It is a union of exactly two induced blocks meeting there, with $x$ and $y$ on opposite sides. Each wing is a single edge or remains nonbipartite after deleting its middle $w$ and also after deleting its own tip, where these are two separate deletions. At least one wing has the latter property. Independently the whole lower graph remains nonbipartite after deleting either tip separately. This also restricts the branch where the lower graph itself has no cut.
* There is an exact local rank test. The chord strictly lowers bipartite order if and only if **every** maximum bipartite set of **each individual lower wing** contains both its ports. In that case $b(J)+1=b(S)+b(T)$, and the minimum numbers of vertices needed to bipartize the two wings add. If $b(J)=|V|-1$, a cut forces one of its wings to be a single pendant tip edge.
* Weighted lower leaf optima also add exactly after erasing $w$ from the eligible vertices on both sides. This gives an exact test for lower tightness in terms of the two separate lower scores. Choose as the near wing one containing the root. The far wing is rooted at the seam. If the two smaller rooted instances each satisfy their own bound for the restricted marks, both are tight. Restoring eligibility at the seam increases the near-side optimum by the indicator of $w\in A\cup P$ and the far-side optimum by the indicator of $w\in A\cap P$. The two local-bound hypotheses are explicit in this last consequence.
* On a split lower graph, the first form holds if and only if the unrestricted leaf count gains and neither wing consists of an eligible pendant tip. Any second-form certificate forces its tip wing to be that single edge. A proposed first form with that tip eligible can be converted into an equally large lower leaf set by exchanging the tip for the middle in the core. In particular, a second-form certificate at a nonpendant tip forces the lower graph itself to have no cut vertex.
* Applying this last result to the published 12-vertex fixture verifies that its lower graph is a nonbipartite block. The fixture satisfies lower equality, rooted sparsity, horizontal distances and the exact rank drop. Its tip $7$ has a second old neighbor $2$ besides the middle $1$.

The universal leaf gain and existence of an eligible pendant tip in any actual tight split transition remain open in this work. The pendant obstruction alone is conditional. It supplies no counterexample to the first-form conjecture under all its transition hypotheses or to Graffiti.pc 180.

## Finite checks

The searches are reproducible C++ enumeration. Their completeness claims are computational and are separate from the kernel-replayed theorems.

* The direct census over all unlabelled biconnected upper graphs of orders 4–9 found 645 tight rooted, marked horizontal triangle profiles. No lower graph was disconnected by deleting its middle.
* The cut-specific generator chooses an ordered adjacent pair compulsory in every maximum bipartite set in each nonbipartite biconnected wing, or takes a single edge. It glues the first ports and adds the chord between the other two. This is the construction in the proved local rank test. For wing orders at most seven it identified 1,154 nonbipartite ordered wing types and one single edge. The 667,589 resulting nontrivial unordered pairs gave 1,792 rooted-sparse horizontal roots and 707,616 marked profiles.
* With an order-eight wing and one pendant edge, 24,871 rooted wing types gave 486 qualifying roots and 42,156 marked profiles. With order-nine starting blocks, all ordered compulsory adjacent pairs in one representative of each unlabelled block were used, without quotienting the pair by automorphisms. Thus 1,062,340 tested marked constructions can include equivalent choices. They gave 5,796 qualifying roots and 707,328 marked profiles.
* Every marked profile in these three construction searches had lower slack at least one, and each search attained one. Together the searches cover every cut transition of total order at most ten. Indeed the two wing orders sum to the total order plus one. An order-three non-edge wing is impossible because the triangle has no compulsory vertex in its maximum bipartite sets. Larger constructed families reach total order thirteen with both wings of order at most seven.

Run `GENG=/path/to/geng bash search.sh` with nauty 2.9.3 and a C++20 compiler. The program compares its outputs with the stored logs.

## Sources and replay

The project requires Lean 4.19.0 and Mathlib 4.19.0 at `c44e0c8ee63ca166450922a373c7409c5d26b00b`. From an environment with the Mathlib oleans on `LEAN_PATH`, run `bash verify.sh`. Alternatively set `LEAN_BIN` and `MATHLIB_DIR` to a Lean bin directory and a built Mathlib checkout. The replay copies the pinned foundation sources from the enclosing repository checkout, creates a fresh temporary object directory, checks all foundation hashes, strictly recompiles those sources, and invokes Lean's kernel replayer on each new module. The audit rejects unsafe, partial and axiom declarations in those modules and checks the printed axiom sets.

All 58 foundation files match their published Git blobs at `vjdad4m/maths` commit `2c1346a1d88b52e0c54bea121f95d4f6a1e77930`. The per-file paths and blob identities appear in `published-blobs.txt`. See the [published source tree](https://github.com/vjdad4m/maths/tree/2c1346a1d88b52e0c54bea121f95d4f6a1e77930).

| Module | Direct imports | Principal result |
|---|---|---|
| PatchRank180 | CyclicRank180 | Rank-preserving deletion in a bipartite two-port patch |
| OddPatch180 | PatchRank180 | Bipartite patches collapse in a rooted-sparse block |
| Seam180 | OddPatch180, FirstForm180 | Location of any seam and compulsory vertices in every maximum lower witness |
| OddWing180 | Seam180, BipartiteSparse180 | Odd-block alternative and the two separate surviving obstructions in a nontrivial wing |
| WingRank180 | Seam180 | Exact rank-drop test on both individual wings |
| OddDeficit180 | OddWing180, WingRank180 | Additive bipartization deficit and pendant consequence at deficit one |
| SeamBudget180 | WingRank180 | Exact eligible-leaf and lower-tightness formulas |
| TightWing180 | SeamBudget180 | Conditional simultaneous local equality and the exact seam losses |
| WingCertificate180 | Seam180, CoreSplit180 | Exclusion of the first form for an eligible pendant tip |
| SeamFirst180 | WingCertificate180, OddWing180 | Exact first-form criterion on a split lower graph |
| OddCase12 | SeamFirst180, Example180 | Application to the existing tight 12-vertex transition |
