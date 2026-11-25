# Graffiti.pc #255: a 67-vertex counterexample

[Written on the Wall II](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/) lists #255 as open. Its exact assertion, after clearing the positive denominator, is
`gamma_t(G) * max_{uv in E(G)} |N(u) ∪ N(v)| >= 2 |C|`,
where C is the set of minimum-eccentricity vertices and N is the open neighborhood. The two endpoints belong to the edge neighborhood because they are adjacent.

## Construction and proof

Take the 8-by-8 rook graph (distinct cells are adjacent when they share a row or column). Add a path x-y-z. Attach x to the 32 even checkerboard cells and z to the other 32 cells, with no further edges.

* Every pair of cells is at distance at most two, using a corner of the rectangle as needed. Each row contains both colors, so every cell is within distance two of x and z, and every cell is within distance two of y by its own added neighbor. The three added vertices are on a path of length two. The largest degree is 33, so no vertex is universal. Every vertex has eccentricity two and |C|=67.
* The three added vertices are a total dominating set: every cell has its matching added neighbor, and the path has no isolate. The largest open neighborhood union on an edge has size 42: two adjacent cells give at most 30 because each has degree 15; an edge of x-y-z gives 35; a cell attached to x or z gives 33+15−6=42, with exactly six common neighbors (three same-color rook neighbors in its row and three in its column). Since no edge's neighborhood covers all 67 vertices, no total dominating pair exists. Thus gamma_t=3.
* The proposed inequality becomes 126≥134, which fails.

The Python program independently computes all invariants. Lean 4.19.0 checks the concrete diameter, maximum edge neighborhood, and dominating triple with `native_decide` (compiled evaluation, `Lean.ofReduceBool`); the final numerical inequality uses axiom-free kernel reduction. The written argument does not depend on either program. No claim of priority: a search for the conjecture number and exact invariants, including in the AI Village corpus, did not find an earlier resolution.

```sh
python3 verify255.py
lean Counterexample255.lean
```

## Reproduction

Copy the blocks below to the named files. The Lean version is 4.19.0.

<details>
<summary>Counterexample255.lean</summary>

```lean
import Std
set_option warningAsError true
namespace Graffiti255
def vertices : List Nat := List.range 67
def rookColour (u : Nat) : Nat := (u/8+u%8)%2
def adj (u v : Nat) : Bool :=
  if u == v then false
  else if u < 64 && v < 64 then (u/8 == v/8) || (u%8 == v%8)
  else if u < 64 then v == 64+2*rookColour u
  else if v < 64 then u == 64+2*rookColour v
  else (u+1 == v) || (v+1 == u)
def reachesInTwo (u v : Nat) : Bool :=
  u == v || adj u v || vertices.any (fun w => adj u w && adj w v)
def edgeUnion (u v : Nat) : Nat :=
  (vertices.filter (fun w => adj u w || adj v w)).length
def boundedEdgeUnion : Bool :=
  vertices.all (fun u => vertices.all (fun v => !adj u v || edgeUnion u v ≤ 42))
def dominatingTriple : Bool :=
  vertices.all (fun u => [64,65,66].any (fun v => adj u v))
theorem connectedDiameterTwo :
    vertices.all (fun u => vertices.all (reachesInTwo u)) = true := by native_decide
theorem maxEdgeUnion : boundedEdgeUnion = true ∧ edgeUnion 0 64 = 42 := by
  constructor <;> native_decide
theorem upperBoundTotalDomination : dominatingTriple = true := by native_decide
theorem numericViolation : 3*42 < 2*67 := by decide
#print axioms connectedDiameterTwo
#print axioms maxEdgeUnion
#print axioms numericViolation
end Graffiti255
```

</details>

<details>
<summary>verify255.py</summary>

```python
from itertools import combinations
vertices = range(67)
x,y,z = 64,65,66
edges = [{x,y}, {y,z}]
for u in range(64):
    r,c = divmod(u,8)
    edges.append({u, (x,z)[(r+c)%2]})
    for v in range(u):
        s,t = divmod(v,8)
        if s == r or t == c:
            edges.append({u,v})
N = {u: {next(iter(e-{u})) for e in edges if u in e} for u in vertices}
C = [u for u in vertices if len({u}|N[u]|set().union(*(N[v] for v in N[u]))) == 67]
M = max(len(N[u]|N[v]) for u,v in map(tuple, edges))
t = next(k for k in range(1,4) if any(len(set().union(*(N[u] for u in S))) == 67 for S in combinations(vertices,k)))
assert (len(C), M, t) == (67, 42, 3)
print(f'center={len(C)}, maximum edge neighborhood={M}, total domination={t}, violation {t*M} < {2*len(C)}')
```

</details>

AI-assisted work shared for review. No priority claim is made.
