# Graffiti.pc #271

[Graffiti.pc catalogue](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/), with the [exact statements](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json) and [definitions](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/definitions.json).

All graphs are finite, simple and connected. Write (t=γ_t(G)), where a total dominating set (D) is a set such that every vertex, including vertices in (D), has a neighbor in (D). Assume order (n ≥ 2), so (t ≥ 2). Let (L) be the maximum number of leaves of a spanning tree.

## Shared connected-domination lemma

Every component of (G[D]), for a minimum total dominating set (D), has at least two vertices. Let (q≤ ⌊ t/2⌋) be the number of these components. Assign each vertex of (G) to a component that either contains it or contains a neighbor, taking the component itself for vertices of (D). The graph on components joined by edges between their assigned classes is connected. A spanning tree of this graph gives (q-1) links. Each such edge between classes yields a walk of length at most three joining vertices of the corresponding components, adding at most two vertices outside (D). Together with (D), these links give a connected dominating set (Z) with
```text
|Z|≤ t+2(q-1)≤ t+2⌊ t/2⌋-2.
```
In particular the estimate (γ_c≤2t-2) is the established bound of Favaron and Kratsch (1991); see [Haynes and Henning](https://doi.org/10.1016/j.disc.2025.114884) for its generalization.

Extend a spanning tree of (G[Z]) by attaching every vertex outside (Z) to a neighbor in (Z). The resulting spanning tree (T) has at least (n-|Z|) leaves and diameter at most (|Z|+1). Thus
```text
 n≤ L+t+2⌊ t/2⌋-2;  diam T≤ 2t-1.
```
In particular, (radG≤radT≤ t), using (radT=⌈diamT/2⌉). If (t=2) or (3) then (q=1), so in that case (diamG≤ t+1).

## #271. Distance between maximum-degree vertices

Let (M) be the set of maximum-degree vertices and (m=max{d_G(x,y): x,y ∈ M}), allowing (x=y). Then (2m≤ t^2), equivalent to the catalogue's (⌈√(2m)⌉≤ t).

For (t ≥ 4), use (m≤ diamG≤2t-1), giving (2m≤4t-2≤ t^2). For (t=3), use (diamG≤ t+1=4), also enough. If (t=2), take a total dominating pair (u,v); their open neighborhoods cover the graph, so (deg(u)+deg(v) ≥ n) and (2Δ ≥ n). If two vertices (x,y ∈ M) were at distance at least three, their neighborhoods would be disjoint and would exclude (x,y). Then (2Δ=deg(x)+deg(y)≤ n-2), a contradiction. Therefore (m≤2) also in the last case.

## Verification scope

The shared Lean file below checks numerical lemmas, not the full graph arguments. Copy it as Arithmetic.lean and run Lean 4.19.0.

<details>
<summary>Arithmetic.lean</summary>

```lean
import Std
namespace Graffiti260

theorem leaves_ge_four (n t L X : Nat) (ht : 2 ≤ t) (hL : 4 ≤ L)
    (hn : n + 2 ≤ L + 2*t) (hX : X+2 ≤ n) :
    2*X ≤ t*L := by
  let a := t-2
  let b := L-4
  have ha : t = a+2 := by dsimp [a]; omega
  have hb : L = b+4 := by dsimp [b]; omega
  calc
    2*X ≤ 4*a+2*b+8 := by omega
    _ ≤ a*b + (4*a+2*b+8) := by omega
    _ = t*L := by rw [ha,hb]; simp only [Nat.add_mul,Nat.mul_add]; omega

theorem periphery_leaves_three (n t b X : Nat)
    (h1 : X ≤ 3*b) (h2 : X+b ≤ n)
    (hn : n ≤ 1+t+2*(t/2)) : 2*X ≤ 3*t := by
  by_cases h : t % 2 = 0
  · have he : t = 2*(t/2) := by omega
    omega
  · omega

theorem max_degree_pair_arithmetic (t d : Nat) (ht : 2 ≤ t)
    (hd : d+1 ≤ 2*t) (h2 : t = 2 → d ≤ 2) (h3 : t = 3 → d ≤ 4) :
    2*d ≤ t*t := by
  by_cases e2 : t=2
  · subst t
    have := h2 rfl
    omega
  by_cases e3 : t=3
  · subst t
    have := h3 rfl
    omega
  let a := t-4
  have ha : t=a+4 := by dsimp [a]; omega
  calc
    2*d ≤ 8*a+16 := by omega
    _ ≤ a*a + (8*a+16) := by omega
    _ = t*t := by rw [ha]; simp only [Nat.add_mul,Nat.mul_add]; omega

theorem degree_two_HH_bound (n : Nat) (hn : 3 ≤ n) :
    (2*n)/3 ≤ 2*((n-2)/3+1) ∧ (2*n)/3 ≤ 2*(n/3+1) := by omega

#print axioms leaves_ge_four
#print axioms periphery_leaves_three
#print axioms max_degree_pair_arithmetic
#print axioms degree_two_HH_bound
end Graffiti260
```

</details>

AI-assisted work shared for review. No priority claim is made.
