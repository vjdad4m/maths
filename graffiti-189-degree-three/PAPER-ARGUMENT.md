# Graffiti.pc #189 at actual second degree 3 (paper deduction)

This is a mathematical draft, not a Lean-certified end-to-end result.
We use Easwar–Johari Theorem B(2)–(4), [arXiv:2609.11719v1](https://arxiv.org/html/2609.11719v1).
Those results cover order at most 9 at d=3 and all articulation graphs.
The remaining graph is 2-connected with minimum degree 2 or 3.
Choose a minimum-degree root r; A,B,C,D denote its distance 1,2,3,4
layers. The finite reduction in `SmallSeparator189` already proves
diameter at most four. Since n≥10, C is nonempty and B has at least 2
vertices. Also |B|+|D|≤3, and hence if D is nonempty, B=2 and D=1.

For a∈A write B(a)=N(a)∩B and C(a)=N(B(a))∩C. Each c∈C belongs
to some C(a), by geodesic predecessors. Every C(a) vertex is at
distance two from a. A nonneighbor of a in A is also at distance two
via r, as is a missing B vertex that meets any adjacent A vertex.
All these charges are distinct. Every C vertex has at least one
B neighbor. Whenever B has two vertices, each has an A neighbor and
their A-neighbor sets together cover at least two A vertices: if
one A vertex were the only A-to-B interface, it would be a cut vertex.
Hence there is a B-to-A matching of size two.

## 1. Minimum degree 2

The root r is the only low vertex; all other degrees are at least 3.
Write A={a1,a2}.

- If a1a2 is absent, both |B(ai)|≥2, and each |C(ai)|≤2 after charging
  the other A. When B=2, both meet all B, hence |C|≤2. When B=3
  and one A meets all B, also |C|≤2.
- If a1a2 is present, both B(ai) nonempty. Each |C(ai)|≤3-|B|+|B(ai)|
  by charging all missed B. An A vertex meeting all B gives |C|≤3.
  Otherwise, when B=3 each covers ≤2. If either B(ai) is singleton
  the union covers ≤3. With B=2 and no A meeting both B, the interface
  is a perfect matching and both C(ai) cover ≤2.

Thus n≥10 leaves two profiles.

**Radius 3, B=3, C=4.** Both B(ai) have size 2, overlap in one B vertex
b0, and the C(ai) are disjoint 2-sets. Then b0 hits no C, and the other
B vertices b1,b2 each hit their entire C pool. Every C vertex has
one B neighbor and hence internal degree at least 2. Any 4-vertex graph
of minimum degree at least 2 has a 4-cycle (its complement is a
matching); removing a cross-pool cycle edge gives a spanning C path
between the pools. Concatenate
`r–a1–b1–[C path]–b2–a2–b0`.

**Radius 4, B=2, C=4, D=1.** The A edge is present and the A-to-B
interface is a perfect matching by the counts above. Each B contacts
a disjoint C pool of size two. Each C has exactly one B neighbor,
so H=G[C∪D] has minimum degree at least 2. Its order 5 implies a
Hamilton path by ordinary Ore traceability (minimum pair degree sum
at least 4). An endpoint of that path lies in C, and is joined, at its
B neighbor, to one end of the spanning prefix
`b1–a1–r–a2–b2`.

## 2. Minimum degree 3: bound on the third layer

Now |A|=3. If A induces an independent set, each |B(a)|≥2 and
each |C(a)|≤1. If B=2 then all A see all B and |C|≤1. If B=3 and
C=3, each C vertex would need a B port hit by exactly one A (otherwise
one of the three C vertices would be charged twice), so all three B
ports have just one A neighbor. That contradicts each |B(a)|≥2.
Hence this case is covered by the order-9 result.

If A induces exactly one edge a1a2 and the isolated A vertex is a3,
then |B(a3)|≥2, |C(a3)|≤1, and
|C(a1)|≤2−|B(a2)\B(a1)| and conversely. If B(a1)=B(a2), their C union
has size at most 2. If the symmetric difference is 1, the B sets are
nested, hence their C sets are nested and again the union has size at
most 2. If the symmetric difference is ≥2, sum the displayed bounds.
Thus |C|≤3. If B=2 then |C|≤1 by the bound at a3.

If A induces the path a1–a2–a3, put B_i=B(ai), C_i=C(ai).
The leaves have nonempty B_i and |C_i|≤2−|B_2\B_i|. At the center,
|C_2|≤3−|B|+|B_2|.
  * B=2: if the center covers both B, then |C|≤3. If it covers one,
    its pool has size at most 2, and the other B's pool at most 2 via a
    leaf a_i. If the center covers none, the two leaf pools each have
    size at most 2. Thus |C|≤4.
  * B=3: if |B_2|=3 then |C|≤3. If |B_2|=2, the center pool has size
    at most 2. A leaf a_i reaching the unique outside B either sees all
    B (hence |C|≤2) or misses an element of B_2, leaving at most one
    C slot for the outside B pool. Thus |C|≤3. If |B_2|=1 and C_2 is
    nonempty, each leaf contributes at most one element outside C_2:
    either the leaf misses B_2 and is charged an extra B vertex, or
    reaches B_2 and already pays for C_2. Thus |C|≤3. In the remaining
    cases C_2 is empty and the two leaf pools cover at most 4 C.

If A is a triangle, each |C(a)|≤3−|B|+|B(a)|. For B=2, a vertex
covering both gives |C|≤3, otherwise each B pool has size at most 2.
For B=3, a vertex covering all three gives |C|≤3; if all B(a) are
singletons or empty, again |C|≤3. Otherwise pick size-2 B(a) and another
B(a') containing its missed B vertex. Their C pools cover C and
each has size at most 2. This proves |C|≤4.

Thus only (|B|,|C|,|D|) ∈ {(3,3,0),(2,4,0),(2,3,1),(3,4,0),(2,4,1)}
can survive order≤9.

## 3. Minimum degree 3: routing the surviving profiles

When A induces a path or triangle, H0=G[{r}∪A] is a diamond or K4,
and has a spanning path with any prescribed distinct endpoints in A.
For the diamond, endpoints at its two leaves use the two central
vertices in either order; an endpoint at its A-center and one at a
leaf use the other leaf then r in between.

**B=3, C=3, D empty.** The graph G[C] is connected. Otherwise an
isolated c∈C has degree at least 3 and so meets all B. It pays at
distance two for the two other C and for every A vertex touching B.
At least two A vertices touch B by 2-connectivity, a contradiction.

If G[A] has ≥2 edges, choose a spanning C path with its endpoints
contacting distinct B vertices. For C=P3, each path endpoint has at
least two B neighbors (internal degree one), so choose distinct ports.
For C=K3, there is an incidence matching of size two between C and
B: every C has a B neighbor and at least two B touch C by
2-connectivity. All C vertex pairs can be path endpoints. Let b0
be the unused B, and b1,b2 the routed B endpoints. The pairs
(b0,b1) and (b0,b2) cannot both fail to match distinct A vertices:
failure for either pair, with both neighborhoods nonempty, means
two equal singleton A-neighbor sets. Both failures would therefore
say the same A vertex is the whole A-to-B interface. Choose the
orientation that works, and concatenate
`b0–[H0 spanning path]–b1–[C spanning path]–b2`.

If G[A] has one edge, the bound above gives disjoint pools
C(a1)∪C(a2) (size 2) and C(a3) (size 1). B(a3) contains at least two
B vertices, so the first pool's two vertices each see just the
unique B vertex b1 outside B(a3), giving them minimum C-degree 2.
Then C is a triangle. Let c3∈C(a3), and let b2∈B(a3) touch c3; write
b3 for the remaining B(a3) vertex. Choose the ordering a_i,a_j of
a1,a2 so that a_j touches b1. The route is
`b3–a3–r–a_i–a_j–b1–c1–c2–c3–b2`.

**B=2, C=4, D empty or singleton.** As above no A reaches both B, and
A induces a path or triangle. Each B's C pool has size at most 2:
a leaf of the A-path pays one missing A, its center pays one missed
B when it has one, and a triangle vertex pays one missed B. Thus the
pools both have size 2 and are disjoint. Each C has exactly one B
neighbor, so G[C∪D] minimum degree is at least 2 and order 4 or 5.
Ordinary Ore traceability gives a spanning path with some endpoint
in C. Attach it to a matched B-to-B spanning route through H0.

**B=2, C=3, |D|=1.** A induces at least two edges (the earlier bounds
exclude the other cases). The D vertex sees all C by its degree.
If C contains an edge c1c2, then c3–D–c1–c2 spans C∪D and can be
attached at a B neighbor of c3. If C is independent, each C vertex
is joined to both B and D by its degree. Use two disjoint extensions
from the B endpoints of the H0 connector, of shapes B–C–D–C and B–C.

**B=3, C=4, D empty.** A has ≥2 edges. If A is a triangle, the bound
requires two overlapping size-two B neighborhoods that cover all B,
and their C pools are disjoint of size two. The common B gate has
no C, and the two exclusive B gates each see one full pool. Thus
C has internal minimum degree 2. Give the unused B gate and one
used B gate distinct A ports (the common gate sees both selected
A vertices, while each exclusive gate sees its associated A vertex).
Use H0 between those gates, then the cross-pool spanning C path
(obtain by cutting a cross-pool edge in a 4-cycle) to the other
exclusive B gate.

If A is a path, the bounds above imply B_2 contains at most one
vertex and C_2 is empty. C_1,C_3 partition C into 2-sets. Every B
gate supporting any C belongs to exactly one leaf's B set. If some
B gate has no C, the other two both support an entire pool and C
has internal minimum degree 2. The unused B gate can be matched to
a distinct A port from some used B gate: if B_2 nonempty it reaches
the A center and the used gates reach leaves; otherwise it reaches
some leaf and choose the used gate hitting the other leaf. Use the
same H0-plus-cross-C routing.

If all three B gates see C, the A center has no B neighbors and
the leaf B sets partition B 1+2. Write a1 for the singleton-port
leaf (b1) and a3 for the other leaf (b2,b3). Its two C-pool mates
C_A attached to b1 each have internal C-degree ≥2; the other pool C_B
has internal degree ≥1 because its vertices can see at most two B.
Thus G[C] is connected (any isolated component of order 2 contains
no C_A, impossible because the other component then also has order 2),
and it is not a claw since at least two vertices have internal degree ≥2.
Among the connected 4-vertex graphs, a spanning path with endpoints
in different pools exists unless C is P4 with C_A both internal:
a Hamilton cycle handles C4, diamond, K4; a paw can start at its
leaf in C_B and end at a triangle vertex in C_A; P4 has fixed endpoints,
and C_A vertices cannot be endpoints. Select b3 to contact the
C_B endpoint and use b2 as the unused prefix endpoint as before.

In the exceptional P4, write its order as cB1–cA1–cA2–cB2.
Both C_B endpoints meet both b2,b3 since their internal degree is
one and ambient degree at least three. Use
`b3–a3–r–a2–a1–b1–cA1–cB1–b2–cB2–cA2`.
