# Graffiti.pc #180 on prime graphs and substitutions

For every connected finite simple graph of order at least two that becomes bipartite after deleting at most one vertex, **both published rooted tests hold at every root**. The same conclusion holds when the endpoints of an edge meet every odd cycle. In both classes the stronger witness defined below works without the adjacent-twin credit.

These conclusions, and ordinary #180, also hold after replacing **every vertex by any nonempty finite graph**, with complete joins between bags on adjacent quotient vertices and no edges between other bags. The internal edges, sizes and odd-cycle-transversal numbers of the bags are unrestricted. The theorem also covers a class of nonadjacent two-vertex transversals described below. The unrestricted conjecture remains open in this work.

Ordinary #180 asserts that `L_s(G) + b(G) ≥ 1 + α(G) + max_r E(r)`. Here `L_s` is the maximum number of leaves in a spanning tree, `b` is the maximum order of an induced bipartite subgraph, `α` is the independence number, and `E(r)` counts vertices at even shortest-path distance from `r`, including `r`.

## The common witness

Choose a root `r`, an independent set `A`, and either distance parity from `r`. Write `P` for that parity class and `K = A ∩ (P ∪ {r})`. Write `U` for `A ∪ P` with the root removed unless it belongs to both marks. Let `W(U)` be the maximum number of vertices from `U` that are leaves of a spanning tree. The formal predicate `Protected` asks for a set `Z` inducing a bipartite graph with

```text
K ⊆ Z                 1 + |A| + |P| ≤ W(U) + |Z|.
```

The first published test pins `A ∩ P`. The exceptional test uses odd `P` and `r ∈ A`, pins `r` as well, and credits one extra vertex when the root is isolated in the induced bipartite witness. Thus `Protected` implies both exact tests. In particular, the conclusions concern *all independent markings*, including markings that cannot be contained in any globally maximum bipartite witness after the root is pinned. The comparison is with the two tests in the [published prime reduction](https://github.com/vjdad4m/maths/tree/1e9169a12a72e3f83e376debe1b0f71f50188563/graffiti-180-prime).

## Why one transversal vertex suffices

For order at least three, the available deletion budget `n + W(U) − (1 + |A| + |P|)` is at least `deg(t) − 2` for **every** protected vertex `t`. Here negative degree bounds are read as zero. This bound holds without a transversal hypothesis. It applies even when `t` and the root are far apart.

For a doubly marked nonroot vertex, the proof constructs a tree containing every edge incident to `t` whose endpoints have different distance parities. Parents of singly marked vertices still move one original distance level toward the root. Counting their parent edges in a distance prefix pays for all same-layer neighbors of `t`. The branching of the star at `t` pays its remaining degree above two. A separate full-star argument handles the root.

If deleting `t` makes the graph bipartite and `t ∈ K`, keep `t` and delete its neighbors on the cheaper side of a bipartition of `G − t`. This preserves all of `K` and costs at most `floor(deg(t)/2)`. The published unpinned low-rank bound supplies one unit on a nonbipartite graph. Together with the degree bound this covers every degree, including four. If `t ∉ K`, the original deletion suffices.

## Two-vertex transversals and the exact remaining reduction

Suppose `Protected` fails for one marking. Consider **any** two distinct vertices `a,b` whose deletion makes the graph bipartite. They must be nonadjacent. Exactly one of the following descriptions applies.

- Exactly one endpoint belongs to `K`, and its degree is four.
- Both belong to `K`. Write `c = |N(a) ∩ N(b)|`. Then `|deg(a) − deg(b)| + c ≤ 2` and `|N(a) ∪ N(b)| ≥ 6`.

The relevant theorem is `pair_obstruction`. Its premise is failure of the stronger predicate. A failure of either published test entails such a failure for its own marking. The converse implication for the stronger predicate is not needed.

The graph-wide sufficient condition `GoodPair` asks for a two-vertex transversal with adjacent endpoints, or with **both** endpoint degrees different from four and at least one of

```text
|deg(a) − deg(b)| + |N(a) ∩ N(b)| > 2
|N(a) ∪ N(b)| < 6.
```

The theorem `universal_iff_remaining_tests` is an equivalence. Ordinary #180 for all nontrivial finite connected simple graphs is equivalent to the two published rooted tests restricted to connected prime graphs of order greater than two with odd-cycle-transversal number at least two, no `GoodPair`, and roots having no incident dominating edge. Thus the first unresolved transversal number for the rooted tests is two. The ordinary bound on the graph itself was already known for transversal number two.

## Substitution and the exceptional credit

The theorem `substitution_protection` transfers a single rooted witness from a quotient marking given by the image of the independent set. The leaf representatives can include the actual root even when they miss a marked vertex of its bag. The loss in eligible leaves caused by changing the marking is bounded by the number of added marks. Bipartite representatives can then be colored together with the extra doubly marked vertices in their bags. The resulting witness contains every required vertex. A universal quotient vertex yields a dominating edge at the lifted root. The theorem `dominating_protection` handles that case with zero credit. The combined theorem `substitution_class` gives the two rooted tests and the ordinary inequality, without a bound on the order or transversal number upstairs.

At any root having a neighbor `v` with at most one neighbor outside the closed neighborhood of the root, `credit_iff` proves an exact equivalence between the credited and uncredited odd-root tests. An isolated witness can be enlarged by inserting `v` after recoloring the isolated root. Independently, `odd_isolate` verifies the credited odd-root test whenever deleting the root's open neighborhood leaves a bipartite graph.

## Source map

All new declarations use the namespace `Minimal180.Transversals`. The direct imports below use the file stem.

| Module | Direct imports | Checked result |
|---|---|---|
| RootReserve180 | PrimeObstruction180 | Singly marked root degree bound and isolated odd-root witness |
| TwoStars180 | RootReserve180 | Simultaneous root and second parity-changing stars |
| ApexColor180 | RootReserve180 | Same-layer color in a graph made bipartite by vertex deletion |
| ApexStar180 | RootReserve180, ParentFiber180 | Tree retaining the apex star and decreasing singly marked parents |
| ForestWidth180 | ParentFiber180, RootReserve180 | Parent-edge count in a distance prefix |
| LayerPayment180 | ApexStar180, ForestWidth180 | Payment for same-layer edges and vertical branching |
| DegreePayment180 | LayerPayment180 | Degree-minus-two bound for both marks |
| RepairCost180 | RootReserve180 | Protected-set bipartite repair for an arbitrary transversal |
| Protected180 | DegreePayment180, RepairCost180 | Common witness, degree budget and implication to both tests |
| RankOneTests180 | Protected180 | Both tests at transversal number at most one |
| PairObstruction180 | RankOneTests180 | Necessary alternatives at every two-vertex transversal |
| PairTests180 | PairObstruction180 | Edge transversals, good pairs and exact remaining reduction |
| Credit180 | Protected180 | Credit removal with a suitable neighbor of the root |
| BagProtection180 | PairTests180 | Transfer of the common witness for a quotient without a universal vertex |
| DominatingPins180 | RankOneTests180 | Full protection at either endpoint of a dominating edge |
| InflationTests180 | BagProtection180, DominatingPins180 | Unrestricted bag transfer and ordinary #180 for the stated quotient classes |

## Computational search

`Search.cpp` exhausts both exact tests for each qualifying root of each input graph. It identifies nontrivial modules by closure of vertex pairs, finds distance parity by breadth-first search, and computes eligible leaves using connected dominating sets. It enumerates bipartite sets as unions of two independent sets, with a separate table for isolated-root witnesses. Qualifying roots have no incident dominating edge.

| Inputs | Qualifying connected nonbipartite prime graphs | Qualifying roots | First test cases | Odd-root cases |
|---|---:|---:|---:|---:|
| All 273,191 connected unlabeled graphs of orders 3–9 | 150,610 | 950,912 | 79,481,132 | 10,042,998 |
| 13,450 generated labeled graphs of orders 10–16 | 10,174 | 107,524 | 39,154,474 | 4,990,666 |

There were zero failed tests. Every successful odd-root marking in these runs admitted an uncredited witness of sufficient order. In the exhaustive part, 273,500 odd-root markings had **no globally maximum** bipartite witness containing their required pins. The higher-order search uses seed 18019169 and a bipartite remainder with two added vertices. Its counts refer to inputs and may include isomorphic graphs. The search is computational evidence only.

The separate `crosscheck.py` directly enumerates every candidate spanning tree, all vertex subsets and their colorability, and all candidate modules. All seven output counters matched the C++ checker individually on every connected input of orders three through seven. Reproduction requires Python 3, a C++20 compiler and nauty's `geng` (version 2.9.3 was used).

```sh
mkdir -p .build
g++ -O3 -std=c++20 Search.cpp -o .build/search
python3 crosscheck.py /path/to/geng
python3 census.py /path/to/geng 3 4 5 6 7 8 9
python3 targeted.py
```

## Lean replay

Set `MATHLIB_DIR` to a built Mathlib checkout at `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Supply Lean 4.19.0 via `PATH` or `LEAN_BIN`. From the extracted archive run

```sh
sha256sum --check --status bundle.sha256
bash verify.sh
```

The script verifies source hashes, rebuilds all 137 public dependency modules into an empty object directory, compiles the new sources with warnings as errors, and kernel-replays every declaration in each new module. The standalone archive includes all imported project sources. The published blob identifiers are recorded against repository commit `1e9169a12a72e3f83e376debe1b0f71f50188563` in `published-blobs.txt`. The replay logs contain the explicit axiom reports.

## Replay from the repository

Run `bash graffiti-180-transversals/verify.sh` from the repository checkout with `MATHLIB_DIR` set to the built pinned Mathlib checkout and, if needed, `LEAN_BIN` set to the Lean 4.19.0 binary directory. An alternate checkout root can be supplied as the first argument. The verifier reconstructs the foundation from the exact tracked blob hashes before rebuilding.
