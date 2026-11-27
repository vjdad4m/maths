# Graffiti.pc #180 and nonadjacent two-vertex transversals

Both rooted tests hold at every root of a connected graph of order at least two when it has a two-vertex odd-cycle transversal with one endpoint of degree at most three and the other endpoint of degree different from four. Two distinct odd endpoint degrees also suffice, including a difference of exactly two. Two cubic endpoints satisfy the first condition. The same conclusion holds whenever the graph-wide marking constraints below are inconsistent. Each of these criteria proves ordinary #180 after arbitrary nonempty substitutions at all vertices. The unrestricted two-transversal case of the rooted tests remains unresolved.

An eight-vertex prime graph shows why a repair at a fixed nonadjacent pair sometimes **must keep both endpoints and recolor surviving vertices**. That marking attains the required inequality exactly. Independently, the exact separator criterion below describes every repair that keeps the protected vertices and meets the available budget.

## Rooted bounds

Let `r` be a root, `P` either distance-parity class, and `A` an independent set. The eligible set `U` consists of `A ∪ P`, with the root removed unless it is in both sets. Let `W(U)` be the largest number of eligible leaves in a spanning tree. The protected set and deletion budget are

```text
K = A ∩ (P ∪ {r})
B = n + W(U) − (1 + |A| + |P|).
```

A bipartite induced set containing `K` of order at least `n − B` proves the protected bound. It implies both exact tests in the earlier prime reduction, including the exceptional odd-root test. Ordinary #180 asserts `L_s + b ≥ 1 + α + max_r E(r)`, where `E(r)` counts even-distance vertices including the root, `b` is induced bipartite order, and `L_s` is the maximum number of spanning-tree leaves.

The frozen `PairTests180` package supplies both prime tests, the adjacent-transversal theorem and the arbitrary-substitution lift. The independent-color proof below applies its `cheap_side` theorem twice. [Published transversal package](https://github.com/vjdad4m/maths/tree/d24cf4b9f561a8e737a9abbe47faf52d22aba0d1/graffiti-180-transversals) · [Original Graffiti.pc statement, printed page 105](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/wowiiaii.pdf)

## Coloring and repair

Fix a nonadjacent transversal pair `X = {a,b}`, its bipartite remainder `R = V − X`, and any proper two-coloring `c` of that remainder. For a proposed deletion `M` disjoint from `K`, choose colors for the retained tips `X − M`. Each surviving outside vertex adjacent to a retained tip demands a flip if its old color equals the chosen tip color, and demands no flip otherwise.

**The deletion works exactly when some choice of tip colors separates all flip demands from all no-flip demands in the surviving remainder.** Separation means there is no path in `R − M` from one kind of demand to the other. A vertex can make both demands and then a path of length zero witnesses failure. In the forward direction, any two proper colorings on the surviving bipartite remainder differ by a constant flip on each connected component. In the reverse direction, flip precisely the components containing a flip demand. Theorem `separator_iff` includes the cost of deleted tips, the pins and the inequality `|M| ≤ B`. It applies to every independent transversal, with independent colors assigned to all retained tips.

For a hypothetical failure at a two-vertex transversal, the following consequences hold simultaneously.

- Every transversal pair meets the same independent set `K`.
- If only `a` is protected, then `B = 2` and `deg(a) = 4`. Every proper coloring of `R` splits the four neighbors of `a` two and two. In each connected component of `R` the two counts are equal. More generally the conclusion holds on every union of components. If `b` is deleted, after any one further unprotected deletion there is still a path in the surviving remainder between oppositely colored neighbors of `a`.
- If both tips are protected, independently prescribe a color for each of them. Delete outside neighbors matching their tip's color, charging shared neighbors only once. This construction must cost more than `B` for **every** coloring and both choices of tip colors. The frozen degree theorem gives `B ≥ max(2, deg(a)−2, deg(b)−2)`.
- If `B ≥ 3`, both endpoints of **every** transversal pair must belong to `K`. Thus all such endpoints form an independent set and all lie in the chosen parity class, except possibly the root. If `B ≤ 2`, every protected vertex has degree at most four.

A nonadjacent transversal pair containing the root has a stronger restriction. **Every partner of the root must belong to the protected set in every failed marking.** If two partners are adjacent or have opposite distance parities from the root, both rooted tests therefore hold there. Also, when the two endpoints of any transversal pair lie in the same distance layer, both must be protected under a failed marking. These results apply without primeness.

To prove the first restriction, suppose the root alone were protected in its pair. The budget and degree would be two and four. A full root star in the parity graph gains another unit whenever the symmetric difference of the independent and parity marks is nonempty. Thus the independent set is exactly the even parity class. For any tree and independent set `P`, the identity below counts the edges with both ends outside that set.

```text
n + |P ∩ leaves(T)| = 1 + 2|P| + |E(T[V − P])| + Σ(v ∈ P) max(deg_T(v) − 2, 0).
```

Any edge outside the mark with one endpoint outside the root neighborhood can coexist with the entire root star in a spanning tree. The identity would then give a third budget unit. Consequently every edge outside the independent mark lies wholly in the root neighborhood. Nonadjacency places that neighborhood inside the bipartite remainder. Deleting the cheaper of its two colors costs at most two and leaves two independent parts, the whole mark and its surviving complement. This constructs the prohibited repair.

For a positive-distance solo tip, saturation implies that at least two neighbors lie in different distance layers from the tip. Within the **whole** distance layer of the tip, the vertices outside the independent set are exactly its neighbors. This forces both members of any same-layer pair to be protected, since a failed transversal pair is a nonedge.

The fixed-color repair gives the low-endpoint theorem by deleting at most `floor(deg(a)/2) + floor(deg(b)/2)` vertices when both tips are protected. In the one-protected cases the degree-four requirement is decisive.

## Simultaneous constraints on the graph

Use one Boolean variable per vertex for membership in `K`. Edges forbid selecting both ends. Transversal pairs require at least one endpoint. A singleton choice is forbidden whenever the degree or two-and-two color condition fails. The double choice is forbidden whenever the coloring repair costs at most the lower bound above. All these constraints have at most two variables. A failed marking supplies an assignment to all of them, even when there are many transversal pairs.

In particular, if `{t,u}` and `{t,v}` are transversals and `u,v` are adjacent, `t` is compulsory. Two adjacent compulsory vertices prove both tests at every root. The universal theorem `universal_iff_shared_remainder` restricts ordinary #180 exactly to the published rooted tests on the previously outstanding connected prime graphs, at eligible roots admitting such a shared-budget cover in at least one parity. The sharper equivalence `universal_iff_root_partners` adds both constraints on root partners and on pairs in the same layer. A cover supplies a necessary condition for failure.

## An eight-vertex repair

The vertices are `0,…,7`. The edges are

```text
03  04  06  07  14  15  17  25  26  37  46  57
```

The graph is connected and prime. Use root `2`, even parity, and independent set `A = {0,1,2}`. The parity and eligible sets are both `{0,1,2,4,7}`; all three members of `A` are protected. The root has no incident dominating edge. The eligible-leaf optimum is three, the deletion budget is two and the maximum induced bipartite order is six.

The disjoint triangles `0–4–6–0` and `1–5–7–1` each require a deletion. The triangle `0–3–7–0` and the odd cycle `1–4–6–2–5–1` exclude the other candidate pairs. The connected dominating set `{0,5,7}` realizes three eligible leaves. Removing any four eligible vertices isolates a vertex of the remaining core, ruling out four eligible leaves in every spanning tree.

The **entire** family of minimum odd-cycle transversals is `{0,1}, {0,5}, {4,7}, {6,7}`. For the chosen pair `{0,5}`, the degree-four vertex `0` is protected. Vertex `5` is unprotected and must nevertheless survive every repair that meets the budget. The two possible deletions are `{4,7}` and `{6,7}`. In the original remainder the path `1–4–6–2` forces opposite colors on protected vertices `1,2`. In every successful witness the path `1–5–2` forces equal colors on those same vertices. Recoloring part of the remainder is essential even if the two tip colors can be chosen freely.

No transversal pair of this graph meets the earlier `GoodPair` condition. The two stars in its transversal-pair family force both `0` and `7` into a hypothetical marking, because `1,5` and `4,6` are adjacent. Vertices `0,7` are themselves adjacent. This proves both rooted tests at every root and ordinary #180 for all substitutions of this graph. The partial coloring strategy fails on this fixture while #180 holds.

## Formal sources

| Source | Main result |
|---|---|
| ConflictRepair180 | Independent tip colors, union of conflicts and its deletion cost |
| FlipSeparator180 | Exact extension of any fixed coloring up to component flips |
| PairColors180 | Degree-four and two-color rigidity for singleton and double pins |
| ComponentBalance180 | Equality of the two color counts in every closed part of the remainder |
| PairSeparator180 | Exact budgeted separator formulation and necessary surviving paths |
| PairClauses180 | Simultaneous constraints, compulsory centers and substitution consequence |
| LowEndpoint180 | A two-vertex transversal with one low-degree endpoint |
| OddPair180 | Two cubic endpoints or two distinct odd endpoint degrees, including a difference of two |
| SharedBudget180 | One common budget and parity for all pairs, with the exact universal reduction |
| SaturatedLayer180 | Full-layer payment and the same-layer neighbors of a saturated nonroot tip |
| SaturatedRoot180 | Additional reserve for a marked root and coincidence of the marks in the root-solo branch |
| IndependentStar180 | Exact independent leaf identity and simultaneous extension of an edge with a root star |
| RootPairRepair180 | Confinement to the neighborhood and the explicit repair at a sole protected root |
| RootPartners180 | Compulsory root partners, same-layer pairs and the sharpened exact reduction |
| EightBase180 | The finite graph, root distances, independent marking and parity |
| EightPrime180 | Primeness by explicit module distinguishers |
| EightFinite180 | maximum bipartite order and complete list of minimum transversals |
| EightLeaves180 | Exact eligible-leaf optimum using the complementary connected core |
| EightPair180 | The marking, forced retention and the ordinary inequality |
| EightResult180 | Recoloring obstruction, failure of the earlier criterion and all-root conclusion |

## Finite search

The older unpinned `rank_two_root` theorem uses the unrestricted bipartite number and does not supply a witness retaining the protected set. The present implications require retention at the same marking. The ordinary rank-two bound used for the finite example is a separate theorem in the frozen import closure. [Earlier rooted rank-two theorem](https://github.com/vjdad4m/maths/blob/d24cf4b9f561a8e737a9abbe47faf52d22aba0d1/graffiti-180-deficit-one-descent/RankTwoRoot180.lean)

The included C++ programs use nauty `geng -cq` and graph6 input. They filter connected nonbipartite prime graphs to exact odd-cycle-transversal number two and exclude graphs having any previously proved `GoodPair`. No search here is used as a premise in Lean. Through order seven there was no qualifying example where the lone unprotected endpoint had to survive. Order eight is the first order exhibiting that obstruction in this searched class. Order minimality is computational evidence.

At orders seven, eight and nine the old graph class contained 5, 281 and 6,744 graphs respectively. The simultaneous Boolean constraints eliminate 5, 76 and 1,201 respectively. A satisfying assignment for the other graphs certifies only consistency of these necessary conditions. Requiring every root partner and both tips of every same-layer pair to be protected reduces the order-eight count from 1,563 surviving root/parity choices to 1,004, and the order-nine count from 51,652 to 31,068. Per-order counts are in the three search logs. The independent standard-library program `fixture.py` enumerates all spanning trees, induced bipartite subsets and candidate modules of the eight-vertex graph.

```sh
python3 fixture.py
mkdir -p .build
for source in PairProbe CoverProbe SharedProbe; do
  g++ -O3 -std=c++20 "$source.cpp" -o ".build/$source"
  for n in 5 6 7 8 9; do
    /path/to/geng -cq "$n" | ".build/$source"
  done
done
```

## Replay

Supply Lean 4.19.0 via `LEAN_BIN` or `PATH`, and set `MATHLIB_DIR` to built Mathlib at `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Run `bash replay.sh`. It rebuilds the tracked [adjacent-transversal package](../graffiti-180-transversals/) and its exact dependency blobs, then compiles and kernel-replays the 20 new modules in order. The included strict transcripts are from the two byte-identical checked runs against the 153 pinned predecessor objects.
