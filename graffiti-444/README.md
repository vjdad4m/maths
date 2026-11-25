# Graffiti.pc #444: a 38-vertex counterexample

[Written on the Wall II](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/) lists #444 open: the 2-independence number is at most n−floor(d/2), where d is the number of distinct counts of incident K4s over all vertices. A 2-independent set induces maximum degree at most one.

Take a core clique on labels 0,1,2,3. Add these six separate pairs, with an edge joining the two vertices of each pair. The two entries in each row give their core neighbors:
```
0123 | 0
0123 | 01
0123 | 012
0123 | 0123
012  | 01
012  | 3
```
Also add isolated-from-each-other outside vertices with core neighborhoods 123, 023, 013, 012, in multiplicities 1,4,7,10 respectively. No other edges. The graph is connected and the 34 outside vertices form a 2-independent set.

For an outside vertex with q core neighbors and partner sharing r of them, its incident K4 count is choose(q,3)+choose(r,2); for an unpaired vertex the second term is zero. These give seven different counts: 0,1,2,4,5,7,10. For a core vertex, its count is 1 (the core clique) plus, for each outside vertex joined to it, the number of pairs among that outside vertex's other core neighbors, plus, for each matched outside pair joined to it, the number of their other common core neighbors. This gives counts 47,44,39,31, respectively, on the core vertices. Thus d=11, and the asserted upper bound is 38−5=33, below 34.

The Python checker counts actual cliques and checks the witness. Lean 4.19.0 compiles the same concrete graph and verifies the witness and counts with `native_decide` (compiled evaluation, not pure kernel reduction). The written clique count is independent. I found no earlier resolution in the sources searched, which is not a priority claim.

## Reproduction

Copy the blocks below to the named files. The Lean version is 4.19.0.

<details>
<summary>Counterexample444.lean</summary>

```lean
import Std
set_option warningAsError true
namespace Graffiti444
def vertices : List Nat := List.range 38
def coreMasks : List Nat :=
  [15,1,15,3,15,7,15,15,7,3,7,8] ++ [14] ++ List.replicate 4 13 ++
  List.replicate 7 11 ++ List.replicate 10 7
def adj (u v : Nat) : Bool :=
  if u == v then false
  else if u < 4 && v < 4 then true
  else if u < 4 then (coreMasks[v-4]?.getD 0).testBit u
  else if v < 4 then (coreMasks[u-4]?.getD 0).testBit v
  else (u < 16 && v < 16 && (u-4)/2 == (v-4)/2)
def cliqueDegree (u : Nat) : Nat :=
  let ns := vertices.filter (adj u)
  ns.foldl (fun n a => ns.foldl
    (fun m b => if a < b && adj a b then m +
      (ns.filter (fun c => b < c && adj a c && adj b c)).length else m) n) 0
def outer : List Nat := vertices.drop 4
def twoIndependent : Bool := outer.all (fun u => (outer.filter (adj u)).length ≤ 1)
def cliqueDegreeValues : List Nat :=
  (vertices.map cliqueDegree).eraseDups
theorem witness : twoIndependent = true ∧ outer.length = 34 := by native_decide
theorem k4ValueCount : cliqueDegreeValues.length = 11 := by native_decide
theorem strict : 38-11/2 < 34 := by decide
#print axioms witness
#print axioms k4ValueCount
end Graffiti444
```

</details>

<details>
<summary>verify444.py</summary>

```python
from itertools import combinations
# Labels 0..3 form the core clique. Each tuple is the set of its incident core labels.
pairs = [
 ((0,1,2,3),(0,)), ((0,1,2,3),(0,1)), ((0,1,2,3),(0,1,2)), ((0,1,2,3),(0,1,2,3)),
 ((0,1,2),(0,1)), ((0,1,2),(3,)),
]
singles = [(1,2,3)]*1+[(0,2,3)]*4+[(0,1,3)]*7+[(0,1,2)]*10
adj = [set() for _ in range(4+2*len(pairs)+len(singles))]
def edge(u,v):
    adj[u].add(v)
    adj[v].add(u)
for u,v in combinations(range(4),2):
    edge(u,v)
for j,(a,b) in enumerate(pairs):
    u,v = 4+2*j,5+2*j
    edge(u,v)
    for k in a: edge(u,k)
    for k in b: edge(v,k)
for u,triple in enumerate(singles,4+2*len(pairs)):
    for v in triple:edge(u,v)
R = set(range(4,len(adj)))
assert all(adj[u] & set(range(4)) for u in R)
assert all(len(adj[u] & R)<=1 for u in R)
counts=[sum(all(y in adj[x] for x,y in combinations([u,*a],2)) for a in combinations(adj[u],3)) for u in range(len(adj))]
d = len(set(counts))
assert d//2 > 4
print(len(adj),counts,sorted(set(counts)), 'violation:',len(R),'>',len(adj)-d//2)
```

</details>

AI-assisted work shared for review. No priority claim is made.
