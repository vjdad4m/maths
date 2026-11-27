# High-degree triangular ears in the order-33 case of Graffiti.pc #384b

For a finite connected simple graph on more than two vertices, #384b asks whether γ₂(G) ≤ |V(G)| − ⌈|T|/2⌉. Here T is the set of vertex triangle-incidence counts, including zero if realized. A set 2-dominates when every vertex outside it has at least two neighbors in it. At order 33 with 33 distinct counts the target is 16.

In the leaf-and-ear reduction, deleting the leaf z gives a 32-vertex core H with positive, pairwise distinct triangle counts, a five-clique and γ₂(H) = 16. The ear e has exactly two neighbors a,c, and ac is an edge. All degrees, triangle counts and common neighbors below refer to H. Let k be the number of common neighbors of a,c other than e.

## Results

| Condition | Checked conclusion |
| --- | --- |
| k = 0 and some ear endpoint has degree four | γ₂(H) ≤ 15 at order 32, hence γ₂(G) ≤ 16 at order and diversity 33. This covers every attachment of the deleted vertex. The core inequality 2γ₂(H) < |V(H)| holds at every order. [Proof](HighEarFinish33.lean) |
| k ≥ 1 and the leaf attaches to a cubic core vertex | γ₂(G) = 16 under the normalized core hypotheses. [Proof](HighEarShared33.lean) |
| Both endpoints have degree at most five and the leaf attaches to a cubic core vertex | γ₂(G) = 16 under the same hypotheses, including when k = 0. [Proof](HighEarRootCap33.lean) |

In any positive core with distinct counts, a five-clique and 2γ₂(H) ≥ |V(H)|, both ear endpoints have degree at least five whenever k ≠ 2. If an endpoint a has degree four, k must be two, a lies on exactly four triangles, and its two neighbors other than c,e are adjacent to each other and to c. They form a four-clique with a and c. The other endpoint has degree at least five. [Degree-four classification](HighEarDegree33.lean) · [Exclusion of the thin case](HighEarFinish33.lean)

If the leaf attaches at a cubic vertex r and the inequality fails, k must be zero, both endpoint degrees must be at least five and at least one must be at least six. If either endpoint has degree five, r must be the only cubic vertex of H. These conditions are necessary. Existence of a graph in the remaining class is open. Noncubic attachments with both endpoints at least five, and the degree-four case with k = 2 and a noncubic attachment, also remain open here. The general diversity-33 case, smaller diversity, and #384b remain unresolved by this result. [Cubic attachment profile](HighEarRootCap33.lean)

## Why the degree-four case closes

Write t(v) for the number of triangles containing v and D for the neighbors of a other than c,e. Counting edges inside the neighbor set of a gives t(a) = 1 + k + |E(H[D])|. If k = 0 and a has degree four, then D consists of two adjacent vertices s,t and t(a) = 2. The ear already has count one. Every cubic must therefore have count three, so there is at most one cubic.

Fix a five-clique C. At a clique vertex x away from a,c and without a cubic neighbor, a cut can omit x while pinning four clique vertices in a two-against-two split. If the core is extremal, switching the cut on a component shows that deleting the three ear-triangle edges and isolating x leaves an a-to-c path. Every simple a-to-c route avoiding e and x has odd length. An even one could be shortened until its clique contacts lie within two consecutive steps, then joined to the retained clique pins to omit x. Consequently a first exterior neighbor on the path can have no neighbor in D except x. [Component switch](HighEarSwitch33.lean) · [Bypass](HighEarBypass33.lean) · [Parity](HighEarParity33.lean) · [Exterior neighbor](HighEarOdd33.lean)

Since s and t are adjacent, each vertex of C outside {c,s,t} must have a cubic neighbor. Capacity forces a unique cubic u, both s,t in C, both a,c outside C, and N(u) = C ∖ {s,t}. Take t as the omitted clique vertex. An odd path starts a,s and can meet the retained clique only at s. Two distinct contacts would yield an even route by the checked clique path lemma. The path also misses u because all three neighbors of u are in C. Insert t between a and s. This gives an even route that meets C only at t and s, at indices one and two respectively. [Forced layout](HighEarLayout33.lean) · [Detour](HighEarDetour33.lean)

Close the even route through e and alternate its vertices between two sets. The first set contains s and the second contains t and e. Choose x in N(u). Add u to the first set and the other two neighbors of u to the second. Those two see both s and u, and u sees both of them. The omitted x sees s,u on the first side and t and another clique member on the second. Any obstruction to completing the two sets would require a cubic outside both sets. The only cubic is already pinned. This gives the strict inequality. [Final two-color construction](HighEarFinish33.lean)

## The shared edge and the degree-five estimate

A retained leaf supplies one neighbor to its attachment vertex. More generally, the checked predicate `Tight H R` means every core set supplying two neighbors off the set, with one allowed credit at each vertex in R, has size at least half the order. For R empty this is ordinary 2-domination. For the singleton attachment, tightness is equivalent to failure of the rooted exchange in the half-order core.

When k ≥ 1, tightness forces two cubics outside R, one of triangle count two and one of count three. If either is missing, the existing clique-overlap lemma puts the new common neighbor and exactly one endpoint in every five-clique. A two-against-two coloring forces a cubic neighbor of each of the other three clique vertices. If one cubic covers all three, a second coloring pins that cubic and forces a different cubic to cover all three. They would have the same neighbor sets and triangle counts, contrary to injectivity. A cubic leaf root already occupies one of the two scores. [Complementary colorings](HighEarPins33.lean) · [Shared-neighbor theorem and cubic-root lift](HighEarShared33.lean)

When either cubic score is unavailable outside R, the ear edge has k = 0. The path argument gives y in D adjacent to at most one other vertex in D. Thus |E(H[D])| ≤ 1 + binom(deg(a) − 3, 2), and t(a) ≤ 2 + binom(deg(a) − 3, 2). At degree five this gives t(a) ≤ 3. The ear occupies one, so the two endpoints of degree five and the cubic root would need three distinct counts among two and three. The same calculation shows why a second cubic is impossible when even one endpoint has degree five. [Uniform bound and order-33 lift](HighEarRootCap33.lean)

## Replay and dependency map

The 11 new modules form a single import chain in the following order. The first imports the frozen `CubicSquareProfile33`, which brings in the old `CubicCoreStrict33`, `EarAnchor`, `EarExchange33`, `EarFrame33`, `EarOnClique33` and pinned maximum-cut results. The two-domination and triangle-count definitions are those of `Proof384b.lean` in the pinned GitHub replay dependencies.

| Module | Main addition |
| --- | --- |
| HighEarPins33 | Two complementary pin assignments with a shared common neighbor |
| HighEarShared33 | Both cubic scores must occur off all credited vertices, with the cubic-root lift |
| HighEarDegree33 | Exact endpoint triangle formula and degree-four alternatives |
| HighEarSwitch33 | Component switching with four fixed clique pins |
| HighEarBypass33 | Reachability after deleting the ear edges and isolating a safe pivot |
| HighEarParity33 | Shortening an even route and merging its alternating vertices with clique pins |
| HighEarOdd33 | Oddness of routes and the exterior-neighbor restriction |
| HighEarLayout33 | The unique cubic and its complete neighborhood in the thin degree-four case |
| HighEarDetour33 | Inserting the second exterior neighbor to obtain an even route |
| HighEarFinish33 | Strict saving, endpoint degrees and lifting to the catalogue inequality |
| HighEarRootCap33 | Uniform triangle cap, cubic-root restrictions and the degree-five lift |

The reuse is structural. `EarOnClique33.scarce_cliques` gives the initial overlap, `EarOnClique33.mixed_blocker` turns failure of an omitted pivot into a low-degree vertex, and `AnchorParity.even_of_two_contacts` supplies the path exchange. `EarExchange33.exchange_iff` and `EarRoot33.attachment_iff` connect cubic-root tightness to the full graph. The #299 transversal estimate controls one completion, and #397c concerns a different graph operation. Neither supplies the simultaneous color classes and parity statement used here. No external graph enumeration enters the proof. [Shared index](https://github.com/vjdad4m/maths/blob/main/README.md) · [Checked clique restrictions](https://github.com/vjdad4m/maths/blob/main/graffiti-384b-ear-exchange/EarOnClique33.lean)

From the repository root, with Lean and Mathlib v4.19.0 available locally:

```bash
CROSSFOUR_LEAN_BIN=/absolute/path/to/lean/bin \
CROSSFOUR_MATHLIB=/absolute/path/to/mathlib4 \
bash graffiti-384b-high-ears/replay.sh
```

The new source hashes and the original strict axiom-audit log are included.
