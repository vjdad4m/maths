# Degree-six cuts: exact component count

Assume the graph is finite and 2-connected, with at most one vertex below
degree six and with at most seven vertices at even distance from any vertex
(including itself). Fix a,b whose deletion yields at least two components;
these components are the shores. A vertex of a shore is a port of a (of b)
if adjacent to that terminal, and is visible if it is a port of either.
Two-connectivity ensures every shore meets each terminal, and a shore of
order at least two has at least two visible vertices (otherwise its sole
port is a cut vertex).

## Three shores all containing a high a-port are impossible

For three disjoint shores let p_i count their a-ports and q_i count their
vertices at distance exactly two from a. Every high a-port in shore i has
degree at most p_i+q_i+(1 if also a b-port, else 0). Indeed its neighbors
are a, perhaps b, p_i-1 other a-ports, and locally some vertices in q_i.
Two foreign a-port sets are contained in the distance-two set of a tested
port of the third shore. Thus every pair of p's sums to at most six, and
the total of the p's is at most nine. Also the q's sum to at most six.
Three high a-ports exhaust all these bounds, so every p_i=3, every q_i=2,
and all three tested ports are common. If a,b were nonadjacent, b would
use a seventh distance-two slot from a, impossible. The six foreign
ports already fill the distance-two budget of the first tested high
port. It follows that this port is universal in its connected shore:
otherwise a shortest path in that shore from it to a nonneighbor would
supply a local distance-two vertex. Consequently the shore is exactly
the three ports and two distance-two vertices, of order five. The two
vertices not adjoining a both have degree at most five (four internal
neighbors and possibly b), which is impossible.

## The sole low vertex must be a common singleton

If there are at least three shores, the preceding argument for both
orientations implies that each terminal has a shore all of whose ports
are low. All these low ports coincide with the sole possible low
vertex s. Both corresponding shores therefore coincide, and this shore
is the singleton {s}, by the two-connectivity visibility property.

Pick any two other shores C and D. All their vertices are high. The
distance-two set of s contains every visible vertex of C or D, so their
total visible count is at most six. Each shore has order at least five
by the degree bound, hence at least two visible vertices, and therefore
at most four. In particular both contain dark (nonvisible) vertices;
their internal degree is at least six, so both shores have order at
least seven.

### At least one shore has no common port

Suppose C has no common port. Let p and r count its a- and b-ports, so
p+r=m_C, its visible count. For each terminal separately, a high C-port
has a cost of at least six across its terminal's local port and D2
counts, while a high opposite-shore port has cost at least five.
The two local D2 counts sum to at most six, so p+m_D≥5 and r+m_D≥5.
Since m_D≤6−m_C, p,r≥m_C−1, hence m_C≤2. All constraints are tight:
m_C=2, p=r=1, m_D=4, four a-ports in D, and the two local a-D2 counts
sum to six. If a,b were nonadjacent, b would occupy a seventh slot from
a (via s), contradiction. Thus a,b are adjacent.

The sole a-port x of C has six distance-two vertices already: the four
a-ports of D, s and b. No local distance-two vertex is allowed, so x is
universal in C. All other vertices of C are consequently at distance
two from a. C has order at least seven, exhausting six D2 slots there
alone, whereas D has at least one local D2 vertex. Contradiction.

### Both shores have common ports

Pick a common port in each shore. A common high port of a shore with
m visible vertices needs at least 5−m dark neighbors. All these neighbors
are at distance two from both terminals. The two shores contribute at
least four distinct vertices in the intersection of the terminals'
positive-even sets. Thus the union of those sets has size at most eight.
All other off-terminal, off-s vertices have both terminal distances
odd and are at even distance from s: the distance via the nearer
terminal is exactly 1+min(dist(a,v),dist(b,v)). Hence graph order is at
most 3+8+6=17. Both shores already have at least seven vertices, so
both have exactly seven vertices. A dark high vertex is then adjacent
to all six other vertices of its shore. In particular all dark vertices
of C and D are at distance two from both terminals. Their total count
is at least 14−6=8, exceeding either terminal's distance-two cap.
Contradiction.

Therefore deletion of a genuine two-cut leaves exactly two components.

## Replay

Main declaration:
`Graffiti189LongestPath.CrossSaturation.ThresholdSix.component_card_eq_two_at_six`.
Use Lean 4.19.0, Mathlib 4.19.0 and prior objects, particularly the
three verified modules in the preceding arbitrary-cap bounds and
degree-six structural package, including `SixCutHighShore189`.
Run `replay.sh` to validate hashes and compile both modules in order.
All reported axioms are standard only. This is a structural reduction,
not a spanning-path theorem for all two-shore cuts.
