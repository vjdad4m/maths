# A proof of Written on the Wall II conjecture 183

This is the written proof accompanying the Lean formalization. Let G be
connected of order n≥2. Write L for its maximum spanning-tree leaf count, b for
its bipartite number, and γc for its minimum connected domination number.

The [catalogue](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/wowiiaii.pdf)
asks for L+b≥Δ(G²)+2rad(G²). DeLaViña–Waller's Theorems 4 and 5
[paper](https://www.kurims.kyoto-u.ac.jp/EMIS/journals/EJC/Volume_15/PDF/v15i1r33.pdf)
give L+b≥n+1, with L+b≥n+2 if G has a claw. The exact metric reduction in
Reduction183 shows that a counterexample has L+b=n+1, is claw-free, has
radius 3, and has vertices v,w with d(v,w)=3 and d(v,x)≤2 for every x≠w.
We derive a contradiction. Since the metric case forces n≥4, use
γc=n−L, hence **γc=b−1**.

We also use the following direct consequence of the DeLaViña–Waller block
growth algorithm (Lean: `two_gain_from_block`). Let B be a maximal connected
induced bipartite subgraph, and suppose two vertices a,d of B can be removed
leaving a connected induced subgraph which dominates both a and d. If no
exterior vertex has its nonempty neighborhood in B exactly {a,d}, then
L+b≥n+2. Indeed each exterior vertex touching B has neighbors in both
parts (by maximality), so such a vertex still has a neighbor after deletion.
The resulting connected core is a state with initial savings two; each
incremental bipartite block can be added without losing those savings.
Consequently every such removable pair in a hypothetical counterexample has
an **exact blocker**: an exterior vertex with neighborhood in B exactly the pair.

## 1. A large odd hole containing v,w

There is a connected induced bipartite set on six vertices containing v,w.
Write a geodesic v,a,q,w, and choose p with d(a,p)≥3 (as rad G=3).
Since d(a,w)=2 and d(a,v)=1, p differs from both v,w and is at distance
exactly two from v, through a vertex d. The vertices w,q,a,v,d,p are
distinct. Besides consecutive edges, only wp can be present: a−d and q−p,
for instance, would yield a two-step route from a to p; if q−d existed,
q would have the three mutually nonadjacent neighbors a,d,w. This is
therefore an induced P6 or C6.

Choose a maximum-order connected induced bipartite subgraph B containing v,w,
and put k=|B|≥6. It is maximal even without the requirement of containing v,w.
Since G is claw-free and neighborhoods in a bipartite graph are independent,
B has maximum degree at most two. It is a path or an even cycle.

- If B is a path, its two endpoints are removable as above. The exact blocker
  closes an induced cycle C on k+1 vertices containing v,w. It is odd because
  otherwise C itself contradicts maximal order of B.
- If B is an even cycle, select x∈B other than v,w. Its two incident edges both
  give removable pairs and hence exact blockers p,q. The blockers are distinct.
  Replacing x by p,q gives an induced path on k+1 vertices if p,q are
  nonadjacent, contradicting maximal order; if adjacent, it gives an induced
  odd cycle C on k+1 vertices. This new cycle still contains v,w.

In either case let m=|C|=k+1≥7. Since deleting one vertex from an odd
cycle yields a bipartite set on k vertices, b≥m−1 and, by equality,
γc≥m−2.

## 2. Neighborhood profiles relative to C

Label C cyclically by c_i with indices modulo m. A vertex outside C which
touches C must see at least one cyclic neighbor of each C vertex it sees;
otherwise there is a claw at that C vertex. Thus its neighbors form cyclic
runs each of length at least two. The outside vertex cannot see all of C,
which has three independent vertices. Nor can it see just one run of
length two: remove one of those two adjacent vertices from C, choosing one
that is neither v nor w (v,w are nonadjacent), and insert the outside
vertex as a new endpoint. This creates an induced path on m>k vertices
containing v,w, contradicting maximum order of B.

The hole C dominates G. Otherwise connectedness supplies an exterior vertex
y touching C and adjacent to an exterior vertex x anticomplete to C. The
vertex y has at least three C-neighbors, hence two nonadjacent C-neighbors
(the hole has no triangle). Together with x those neighbors give a claw at y.

It follows that every exterior vertex's C-neighborhood has one of these forms:
a run of length 3, a run of length 4, or two disjoint separated runs of length
2. Indeed, a run of length ≥5 contains an independent triple, three runs also
give an independent triple, and a run of length ≥3 together with a second run
does as well.

## 3. Two separated pairs are impossible

Suppose a vertex z has profile {c_i,c_{i+1},c_j,c_{j+1}}, with the forward
gap d from i to j satisfying 3≤d≤m−3. We show three propagation
rules for such a profile:
(i,j)→(i+1,j+1) always; (i,j)→(i+1,j+2) if d≤m−4;
(i,j)→(i+2,j+1) if d≥4.
For each rule write (s,t)=(1,1),(1,2),(2,1) respectively. Delete the two
pairs at starts i+s and j+t from C and add z, obtaining D of order m−3.
The deleted pairs are separated: the new gap d+t−s lies in [3,m−3].
The retained arcs are nonempty, with c_j on the first retained arc after
the first deleted pair, and c_i on the second retained arc after the second
deleted pair. To check those memberships, use d≥s+2 and m−d≥t+2;
these follow from the applicability conditions of the respective rules.
Thus z joins the retained arcs and D is connected. All vertices of C lie in
D or are adjacent to one of the retained arcs: every removed pair has a
retained vertex on either side.

Since γc≥m−2, D fails to dominate some vertex y. This y is exterior,
nonadjacent to z, and all its C-neighbors are deleted vertices. Its profile
must therefore be exactly the two deleted pairs, by Section 2 (each run needs
at least two vertices, and at least three neighbors in total). This proves
the propagation rules.

Rotate by the first rule and vary the gap by the second and third. All ordered
pairs of starts with gap in [3,m−3] now occur as profiles. In particular the
pair of starts at v,w occurs, since d_G(v,w)=3 gives cycle distance at least
three and hence both directed gaps at least three. Its exterior vertex is a
common neighbor of v and w, contradiction.

## 4. A run of length four is impossible

Suppose z has exactly the neighbors c0,c1,c2,c3 on C. Delete respectively
{c1,c2,c3,c4} or {c_{−1},c0,c1,c2} from C and add z. In each case
a connected set of order m−3 results: the remaining cycle arc is a path,
and z attaches to the retained c0 or c3 respectively. The set dominates
all of C (z dominates the three matching removed vertices, and the fourth
has a retained cycle neighbor just beyond it). So in the rightward and
leftward cases take undominated exterior vertices R,L whose C-neighborhoods
are subsets of the respective removed runs, and which are nonadjacent to z.
They are distinct, as the removed runs intersect in only c1,c2 and each
profile has size at least three.

On the right, profile {c1,c2,c3} is impossible: at c3, neighbors z,R,c4
would induce a claw, as both z and R avoid c4 and each other. On the left,
profile {c0,c1,c2} is impossible by the reflected argument at c0. Thus
R sees c2,c3,c4 and possibly c1, and L sees c_{−1},c0,c1 and possibly c2.

The two optional edges are both present exactly when L and R are adjacent.
If L is adjacent to R but avoids c2, there is a claw at R with leaves
L,c2,c4; if R avoids c1, the reflected claw is at L. Conversely, if
either optional edge is present while L and R are nonadjacent, the shared
neighbor c2 or c1 respectively is the center of a claw with leaves L,R,z.

If neither optional edge is present, the following are four induced paths on
m vertices (all exterior edges among L,R,z are absent):
  1. c_{m−2}, c_{m−3}, …, c4, R, c2, z, c0, L.
  2. c5, c6, …, c_{m−1}, L, c1, z, c3, R.
  3. z, c1, L, c_{m−1}, c_{m−2}, …, c4, R.
  4. z, c2, R, c4, c5, …, c_{m−1}, L.
Their omitted cycle triples are respectively {1,3,m−1}, {0,2,4},
{0,2,3}, {0,1,3}. A pair of cycle vertices meeting all four triples must,
as the first two triples are disjoint, have one index a in {1,3,m−1} and
one b in {0,2,4}. If a=1 then b∈{0,2}; if a=3 any b is possible;
if a=m−1 then b=0. Every pair is cyclically adjacent except {0,3},
whose vertices share neighbor z. Thus {v,w} cannot meet all four omitted
triples, and at least one of the displayed paths contains v,w. Its
order m>k contradicts the choice of B.

Therefore both optional edges occur. In particular the 4-run profile forces
profiles at its two cyclic shifts by one, and iterating yields every cyclic
4-run.

## 5. Metric contradiction

By Section 3, C-neighborhoods of all exterior vertices are runs of length
at most four. Such a run cannot contain two cyclically distance-four-or-more
vertices. If m≥9, there are at least two C vertices at cyclic distance at
least four from v (the ±4 positions); at least one is not w. Its distance to
v in G is at most two. It is not adjacent within C and no C vertex is a common
neighbor with v, so an exterior common neighbor would exist, contradiction.

Hence m=7. Of the two C vertices at cyclic distance three from v, one is w
(as d_G(v,w)=3), and the other is within distance two in G. This needs an
exterior common neighbor with v, so Section 3 implies a 4-run profile.
Section 4 forces all cyclic 4-runs, including one containing v and w, a
final contradiction.
