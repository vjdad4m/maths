# Defect amplification without small cyclic cuts

**This is an equivalence within a restricted graph class, not a solution of Kelmans's conjecture.** The class consists of finite simple cubic 3-vertex-connected graphs of order divisible by six in which every edge cut with at least two vertices on each side has size at least four. We use this cut formulation of cyclic 4-edge-connectivity for cubic graphs.

For this class, each of the following guarantees implies the other two:

1. Every graph has a spanning packing of three-vertex paths, not necessarily induced.
2. Every graph has a packing missing at most a fixed number of vertices, independently of its order.
3. For each positive integer $s$, every sufficiently large graph has a packing missing at most a fraction $1/s$ of its vertices.

The precise statements appear in [FourRingCyclicEquivalence.lean](src/FourRingCyclicEquivalence.lean) as `cyclic_bounded_equiv` and `cyclic_vanishing_equiv`.

## Quantitative construction

Suppose a graph of order $n$ in the restricted class has no perfect packing. Remove the ends of one of its edges and put $k$ copies of the resulting cell on a ring. Each cell has four distinct joining vertices, grouped according to the two removed vertices. Join the two outgoing vertices of one cell to the two incoming vertices of its successor by a matching. Take $k$ divisible by six. This preserves the graph class and yields order $k(n-2)$.

Any packing of the ring leaves at least $k$ vertices uncovered; its uncovered fraction is at least $1/(n-2)$. Here is the mechanism. A path crossing a joining edge contributes widths $(1,2)$ or $(2,1)$, counting the vertices on the two sides; an unused edge contributes $(0,0)$. Let $L_i,R_i$ be the total widths at each of the two ends of cell $i$, and $h_i$ its number of uncovered vertices. Then $R_i+L_{i+1}\equiv0$ and $h_i+L_i+R_i\equiv1$, modulo three. If $h_i=0$ and $L_i=R_i=2$, the two removed vertices can complete the cell's fragments to a full packing of the original graph. Thus this state is forbidden. With $\phi(x)=(1-x)\bmod3$ in $\{0,1,2\}$, each term $h_i+\phi(L_{i+1})-\phi(L_i)$ is at least one: it is congruent to one, and the only possible negative case is that forbidden state. The differences telescope around the ring.

For small cuts, a split cell contributes at least two internal edges. Two split cells already cost four. If no cell is split, a nonempty proper cut of the circular sequence crosses at least two pairs of joins. If exactly one cell is split and the other cells do not all lie on one side, there is at least one more pair of joins. In the remaining case, the minority side lies within the split cell and has the same boundary as it does in the original graph with the two removed vertices restored on the other side. Its size must be one. Lean also verifies 3-vertex-connectivity separately.

## Relation to earlier work

The construction uses familiar four-pole and cyclic-join ideas. See [Kelmans's paper, §§2 and 3](https://arxiv.org/abs/0910.2766) for packing arguments with interfaces, [Goedgebeur et al.](https://backoffice.biblio.ugent.be/download/8637147/8637151) for four-edge joins and cyclic cuts, and [*Cubic graphs that cannot be covered with four perfect matchings*](https://doi.org/10.1016/j.jctb.2021.04.004) for cyclic arrangements of multipoles in a different setting. No priority claim is made.

The sibling [three-port amplification](../kelmans-defect) handles all cubic 3-vertex-connected graphs, without a cyclic-connectivity restriction. It does not reduce that larger class to the restricted class here. Indeed the three-port construction creates a nontrivial cut of size three.

## Replay

From a Lean 4.19.0 project with Mathlib 4.19.0 and its build cache:

    lake env bash /path/to/maths/kelmans-defect-cyclic/replay.sh

The script replays the unchanged sibling proof dependencies and the full new source closure in a temporary build directory, with warnings treated as errors.

## Fixed girth bounds

The same equivalences hold **at every fixed girth threshold** within the restricted class. The construction needs no additional short cycles: [FourRingGirth.lean](src/FourRingGirth.lean) proves that each cycle in the ring gives a cycle of no greater length in the original graph. [FourRingGirthEquivalence.lean](src/FourRingGirthEquivalence.lean) proves the uniform-vanishing and bounded-defect equivalences with the girth hypothesis on both sides. These statements do not transfer the assertion to graphs with small cyclic cuts or smaller girth.

[FourRingStandardEquivalence.lean](src/FourRingStandardEquivalence.lean) states these fixed-girth equivalences directly using Mathlib's girth and the absence of cuts of at most three edges with a cycle on each side. [FourRingCyclicGeometry.lean](src/FourRingCyclicGeometry.lean) and [FourRingGirthGeometry.lean](src/FourRingGirthGeometry.lean) verify the translations to the cut and cycle formulations used in the construction.
