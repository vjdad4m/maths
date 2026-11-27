import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Multiset.Sort
import Mathlib.Combinatorics.SimpleGraph.Clique
import Lean.Elab.Tactic.Omega

/-! A counterexample to AutoGraphForge physical row 2223. -/
namespace ThreeLeaves2223
open SimpleGraph Finset

noncomputable def degreesDesc {U : Type*} [Fintype U] (G : SimpleGraph U) [DecidableRel G.Adj] :=
  (univ.val.map (fun v => G.degree v)).sort (· ≥ ·)

/-- A walk attaining the table entry exists if a neighbor decreases it by one. -/
theorem metric_certificate {U : Type*} {G : SimpleGraph U} (d : U → U → ℕ)
    (zero : ∀ x y, d x y=0 ↔ x=y)
    (edgeBound : ∀ x y z, G.Adj y z → d x z ≤ d x y+1)
    (down : ∀ x y, x≠y → ∃ z, G.Adj z y ∧ d x z+1=d x y) :
    (∀ x y, G.Reachable x y) ∧ ∀ x y, G.dist x y=d x y := by
  have attained (x y : U) : ∃ p : G.Walk x y, p.length=d x y := by
    generalize hv : d x y = k
    induction k generalizing y with
    | zero =>
      obtain rfl := (zero x y).mp hv
      exact ⟨.nil,rfl⟩
    | succ k ih =>
      have ne : x≠y := by rintro rfl; have := (zero x x).mpr rfl; omega
      obtain ⟨z,zy,drop⟩ := down x y ne
      obtain ⟨p,eq⟩ := ih z (by omega)
      exact ⟨p.concat zy,by simp [eq]⟩
  have lower {u v : U} (p : G.Walk u v) (x : U) : d x v ≤ d x u+p.length := by
    induction p with
    | nil => simp
    | cons e p ih =>
      have step := edgeBound x _ _ e
      simp only [Walk.length_cons]
      omega
  have reach (x y : U) : G.Reachable x y := (attained x y).choose.reachable
  refine ⟨reach,fun x y => ?_⟩
  obtain ⟨p,eq⟩ := attained x y
  obtain ⟨q,short⟩ := (reach x y).exists_walk_length_eq_dist
  have lb := lower q x
  rw [(zero x x).mpr rfl,zero_add,short] at lb
  exact le_antisymm ((SimpleGraph.dist_le p).trans_eq eq) lb

/-- The GraphCalc loop searches all prefix lengths from zero to the graph order,
and returns None if no prefix has a large enough degree sum. -/
noncomputable def subTotal? {U : Type*} [Fintype U] (G : SimpleGraph U) [DecidableRel G.Adj] :
    Option ℕ :=
  (List.range (Fintype.card U + 1)).find? fun k =>
    decide (Fintype.card U ≤ ((degreesDesc G).take k).sum)

abbrev V := Fin 11

/-- The seven path levels contain two vertices at level 0, four at level 2, and one elsewhere. -/
def level (x : V) : ℕ := if x.val < 7 then x.val else if x.val = 7 then 0 else 2

def graph : SimpleGraph V where
  Adj x y := level x + 1 = level y ∨ level y + 1 = level x
  symm _ _ e := e.symm
  loopless _ := by simp

instance : DecidableRel graph.Adj := fun x y => inferInstanceAs
  (Decidable (level x + 1 = level y ∨ level y + 1 = level x))

def TriangleFree {U : Type*} (G : SimpleGraph U) := ∀ x y z, G.Adj x y → G.Adj y z → ¬ G.Adj z x

theorem triangle_free : TriangleFree graph := by
  intro x y z xy yz zx
  change level x + 1 = level y ∨ level y + 1 = level x at xy
  change level y + 1 = level z ∨ level z + 1 = level y at yz
  change level z + 1 = level x ∨ level x + 1 = level z at zx
  omega

set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

/-- Distinct vertices of a common level are two edges apart. Paths between
different levels can be chosen monotone. -/
def d (x y : V) : ℕ :=
  if x = y then 0 else if level x = level y then 2
  else max (level x) (level y) - min (level x) (level y)

theorem metric : (∀ x y, graph.Reachable x y) ∧ ∀ x y, graph.dist x y = d x y :=
  metric_certificate d (by decide) (by decide) (by decide)

theorem connected : graph.Connected := ⟨metric.1⟩

theorem subTotal_exact : subTotal? graph = some 2 := by
  let L := [6,5] ++ List.replicate 6 2 ++ [1,1,1]
  have degreeList : degreesDesc graph = L := by
    unfold degreesDesc
    rw [Finset.val_univ_fin, Multiset.map_coe, Multiset.coe_sort]
    have eq : (List.finRange 11).map (fun v => graph.degree v) =
        [1,6,2,5,2,2,1,1,2,2,2] := by decide
    rw [eq]
    simp [List.mergeSort,L]
  unfold subTotal?
  rw [degreeList]
  decide

theorem k4_free : graph.CliqueFree 4 := by
  by_contra no
  obtain ⟨f⟩ := (not_cliqueFree_iff 4).mp no
  have edge {x y : Fin 4} (h : x ≠ y) : graph.Adj (f x) (f y) :=
    f.map_adj_iff.mpr ((top_adj x y).mpr h)
  exact triangle_free (f 0) (f 1) (f 2)
    (edge (by decide)) (edge (by decide)) (edge (by decide))

/-- The maximum over ordered distinct triples equals the maximum over the
unordered distinct triples in GraphCalc, by symmetry of undirected distance. -/
noncomputable def triameter {U : Type*} [Fintype U] [DecidableEq U] (G : SimpleGraph U) :=
  univ.sup fun a => (univ.erase a).sup fun b =>
    ((univ.erase a).erase b).sup fun c => G.dist a b + G.dist b c + G.dist c a

theorem triameter_exact : triameter graph = 14 := by
  have eq : graph.dist = d := funext fun x => funext (metric.2 x)
  unfold triameter
  rw [eq]
  decide

/-- GraphCalc triameter has a numerical value on connected inputs, and the
sub-total routine returns an option. The witness meets both domain conditions. -/
theorem row2223_false : ¬ (∀ (U : Type) [Fintype U] [DecidableEq U]
    (G : SimpleGraph U) [DecidableRel G.Adj] (s : ℕ), 2 ≤ Fintype.card U →
    G.CliqueFree 4 → G.Connected → subTotal? G = some s → triameter G ≤ 4*s+4) := by
  intro conjecture
  have bound := conjecture V graph 2 (by decide) k4_free connected subTotal_exact
  rw [triameter_exact] at bound
  omega

#print axioms connected
#print axioms k4_free
#print axioms subTotal_exact
#print axioms triameter_exact
#print axioms row2223_false

end ThreeLeaves2223
