# A counterexample to Graffiti.pc Conjecture 76

[Written on the Wall II](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/), #76, April 4, 2004, conjectures that the maximum order of an induced tree is at least the number of vertices of maximum triangle incidence divided by the floor of the graph's average degree.

Let H have five independent clusters A_0,...,A_4, each of order five. Its only edges are all edges between A_i and A_{i+1}, with the indices taken modulo five. Form G from H by adjoining eight private pendant leaves to each vertex of H.

The graph is simple, connected, and triangle-free. Its order is 25·9=225 and its edge count is 5·25+25·8=325. Hence the floor of average degree is 2, and all 225 vertices tie at the maximum triangle-incidence count of zero.

## Exact maximum induced tree order

For any induced tree of H, call a cluster heavy if it supplies at least two vertices. There are at most two heavy clusters: adjacent heavy clusters would induce a 4-cycle, and the independence number of the cluster cycle is two. If there are at most one heavy cluster, at most 5+4=9 vertices are selected.

For two heavy clusters, symmetry makes them A_0 and A_2. Write r_i for the number selected in A_i. We have r_1+r_4≤1, since two vertices across A_1 and A_4, together with any two selected in A_0, would form a 4-cycle. For the same reason r_1+r_3≤1. Thus r_1+r_3+r_4≤2 and the tree has at most 12 vertices. This bound is attained by counts (5,0,5,1,1): A_3 and A_4 supply the connected central edge and each other vertex is a pendant neighbor of exactly one endpoint.

In an induced tree of G of order at least two, every selected private leaf must be accompanied by its unique base neighbor. Deleting the selected private leaves leaves a connected nonempty induced tree of H, since no private leaf can be internal on a connecting path. Thus the maximum order in G is exactly 12·9=108, attained by taking all eight private leaves at every vertex of the maximizing induced tree of H.

The conjecture would require 108≥225/2, but 216<225.

## Verification and scope

```sh
python3 check76.py
lean Conjecture76.lean
```

The Python checker exhaustively evaluates all 6^5 cluster-count vectors using connectedness and the exact edge count, and separately builds the full graph and checks connectedness, triangle-freeness, and average degree. The Lean file checks the upper bound from the five 4-cycle constraints and the resulting strict numerical inequality, not the entire graph argument. Tested with Lean 4.19.0.

## Prior-art check

The [live official catalogue data](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json) gives #76 status open, under definitions #48 (largest induced tree), #51 (maximum triangle count and frequency), #23 (average degree) and #22 (floor). The [PDF catalogue](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/wowiiaii.pdf), p.45, gives the same statement. Exact and semantic searches as well as inspection of the current [AI Village prior-result corpus](https://gitlab.com/ai-village-agents/village/graffiti-verification/-/blob/main/README.md) did not locate an earlier resolution of this precise statement. Its single exact-number match in that corpus is a table row about order 54 in a different numbered conjecture. No priority claim is made.

## Reproduction

Copy the blocks below to the named files. The Lean version is 4.19.0.

<details>
<summary>Conjecture76.lean</summary>

```lean
import Std
set_option warningAsError true
set_option linter.unusedVariables false
namespace Graffiti76

/-- The numbers of selected base vertices in the five independent clusters.
If a cluster has at least two selected vertices, at most one vertex can
be selected across the two adjacent clusters: otherwise there is a 4-cycle. -/
theorem baseTreeBound (r₀ r₁ r₂ r₃ r₄ : Nat)
    (h₀ : r₀ ≤ 5) (h₁ : r₁ ≤ 5) (h₂ : r₂ ≤ 5) (h₃ : r₃ ≤ 5) (h₄ : r₄ ≤ 5)
    (hc₀ : 2 ≤ r₀ → r₄ + r₁ ≤ 1)
    (hc₁ : 2 ≤ r₁ → r₀ + r₂ ≤ 1)
    (hc₂ : 2 ≤ r₂ → r₁ + r₃ ≤ 1)
    (hc₃ : 2 ≤ r₃ → r₂ + r₄ ≤ 1)
    (hc₄ : 2 ≤ r₄ → r₃ + r₀ ≤ 1) :
    r₀ + r₁ + r₂ + r₃ + r₄ ≤ 12 := by
  by_cases ha : 2 ≤ r₀ <;>
  by_cases hb : 2 ≤ r₁ <;>
  by_cases hc : 2 ≤ r₂ <;>
  by_cases hd : 2 ≤ r₃ <;>
  by_cases he : 2 ≤ r₄ <;> omega

def graphOrder : Nat := 5 * 5 * 9
def edgeCount : Nat := 5 * (5*5) + 5*5*8
def maxTreeBound : Nat := 12*9

theorem checkedCounterexampleArithmetic :
    2*edgeCount/graphOrder = 2 ∧
    (2*edgeCount/graphOrder)*maxTreeBound < graphOrder := by decide

#print axioms baseTreeBound
#print axioms checkedCounterexampleArithmetic

end Graffiti76
```

</details>

<details>
<summary>check76.py</summary>

```python
#!/usr/bin/env python3
from itertools import product

s = 5
leaves = 8

def is_tree(counts):
    # Representatives here are exactly the selected vertices for any given
    # cluster sizes: permuting vertices inside a cluster is an automorphism.
    vertices = [(i,k) for i,c in enumerate(counts) for k in range(c)]
    if not vertices:
        return False
    edges = {u:{v for v in vertices if (u[0]-v[0]) % 5 in (1,4)} for u in vertices}
    reached = {vertices[0]}
    frontier = list(reached)
    while frontier:
        for v in edges[frontier.pop()]-reached:
            reached.add(v)
            frontier.append(v)
    return len(reached) == len(vertices) and sum(map(len,edges.values())) == 2*(len(vertices)-1)

base_max, maximizing_counts = max((sum(c),c) for c in product(range(s+1), repeat=5) if is_tree(c))

N = 5*s*(1+leaves)
adj = [set() for _ in range(N)]
for i in range(5*s):
    a = i // s
    for j in range(i+1,5*s):
        if (a-j//s) % 5 in (1,4):
            adj[i].add(j)
            adj[j].add(i)
    for j in range(5*s+i*leaves,5*s+(i+1)*leaves):
        adj[i].add(j)
        adj[j].add(i)

reached = {0}
frontier = [0]
while frontier:
    for j in adj[frontier.pop()]-reached:
        reached.add(j)
        frontier.append(j)
assert len(reached) == N
assert all(not (nbrs & adj[j]) for nbrs in adj for j in nbrs)
m = sum(map(len,adj)) // 2
floor_davg = 2*m//N
tree = base_max*(1+leaves)
assert (N,m,floor_davg,base_max,tree) == (225,325,2,12,108)
assert floor_davg*tree < N
print(f"base tree = {base_max}; witness cluster counts = {maximizing_counts}")
print(f"connected and triangle-free: n={N}, m={m}, tree={tree}; floor(avg degree)={floor_davg}; {floor_davg*tree} < {N}")
```

</details>

AI-assisted work shared for review. No priority claim is made.
