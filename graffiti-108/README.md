# A counterexample to Graffiti.pc Conjecture 108

**Statement.** Conjecture 108 in Ermelinda DeLaVina's
[Written on the Wall II](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/wowiiaii.pdf)
asserts that every nonempty connected simple graph satisfies
`alpha <= maxEven + 2 floor(alphacore/3)`, where maxEven counts the
vertices at even shortest-path distance from the most favorable source and
alphacore is the size of the intersection of all maximum independent sets.
The November 2026 catalogue snapshot labels it open. No historical priority is asserted. The search and formalization were AI-assisted.

**Witness.** Take the Kneser graph KG(7,3). Its vertices are the 35 triples of
{0,1,2,3,4,5,6} and different vertices are adjacent precisely when disjoint.

**Shortest paths.** Fix a triple A. The distance to B is 0 if B=A, 1 if they
are disjoint, 2 if their intersection has size 2, and 3 if it has size 1.
In the size-2 case the 3-point complement of their union is a common neighbor.
In the size-1 case the complement of their union has only two points, so no
common neighbor exists. Write X=A\B and Y=B\A, and let p,q be the two
remaining points. The walk A, Y∪{p}, X∪{q}, B has length 3. This proves
connectivity and gives distance-shell sizes 1,4,12,18. Thus maxEven is 13,
including the source at distance 0. Excluding it would only make the
inequality fail more strongly.

**Independence number.** All 15 triples containing a specified point form an
independent set. For an upper bound, index triples lexicographically starting
at 0. The following five disjoint cycles cover all vertices; each displayed
list closes back to its first vertex:

    0 31  4 25 14 15 34
    1 28 11 16 33  2 30
    3 27 22  8 19  7 32
    6 20 29 10 18 12 21
    5 23 26 13 17  9 24

Each cycle contains at most three members of any independent set: every
selected position is followed by a different unselected position, so twice
the selection size is at most seven. Thus alpha is exactly 15.

**Core.** For every vertex (triple), choose a point it does not contain. The
15 triples containing that point form a maximum independent set excluding
the chosen vertex. The core is empty.

Therefore the claimed inequality reduces to **15 <= 13**, which is false.

## Reproduce

- `lean Counterexample108.lean` using Lean 4.19.0, no Mathlib required. From this directory, run `lean -DwarningAsError=true Counterexample108.lean`.
- `python3 verify_counterexample.py` independently reconstructs the graph,
  checks the cycle partition and stars, and checks all shortest distances by BFS.
- `make_counterexample.py` generates the explicit triple and path certificate
  tables embedded in the Lean file. The Lean file independently checks them.
