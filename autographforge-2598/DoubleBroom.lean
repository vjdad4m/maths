import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-! A subcubic tree refutes physical row 2598 of AutoGraphForge. -/
namespace DoubleBroom2598
open SimpleGraph Finset

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

/-- NetworkX sums shortest-path lengths over all ordered pairs. The zero
diagonal contributes nothing, and the denominator counts distinct pairs. -/
noncomputable def orderedDistanceSum {U : Type*} [Fintype U] (G : SimpleGraph U) : ℕ :=
  ∑ u : U, ∑ v : U, G.dist u v

/-- The catalogue uses this value on connected graphs of order at least two. -/
noncomputable def averageShortestPathLength {U : Type*} [Fintype U] (G : SimpleGraph U) : ℚ :=
  (orderedDistanceSum G : ℚ) / (Fintype.card U * (Fintype.card U - 1) : ℕ)

/-- GraphCalc sums this symmetric endpoint weight over the unordered edge set. -/
def harmonicIndex {U : Type*} [Fintype U] [DecidableEq U] (G : SimpleGraph U)
    [DecidableRel G.Adj] : ℚ :=
  ∑ e ∈ G.edgeFinset, Sym2.lift
    ⟨fun u v => (2 : ℚ) / ((G.degree u + G.degree v : ℕ) : ℚ),
      fun u v => by dsimp only; rw [Nat.add_comm]⟩ e

abbrev V := Fin 11

/-- Vertices 0 through 8 form a path. Vertices 9 and 10 duplicate its
endpoints, with neighbors 1 and 7 respectively. -/
def level (v : V) := if v.val < 9 then v.val else if v.val = 9 then 0 else 8

def graph : SimpleGraph V where
  Adj u v := level u + 1 = level v ∨ level v + 1 = level u
  symm _ _ e := e.symm
  loopless _ := by simp

instance : DecidableRel graph.Adj := fun u v => inferInstanceAs
  (Decidable (level u + 1 = level v ∨ level v + 1 = level u))

/-- Different vertices at the same level are sibling leaves. Between
different levels, a monotone path realizes the difference of their labels' levels. -/
def distance (u v : V) := if u = v then 0 else if level u = level v then 2
  else max (level u) (level v) - min (level u) (level v)

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

theorem metric : (∀ u v, graph.Reachable u v) ∧ ∀ u v, graph.dist u v = distance u v :=
  metric_certificate distance (by decide) (by decide) (by decide)

theorem connected : graph.Connected := ⟨metric.1⟩

theorem subcubic : ∀ v, graph.degree v ≤ 3 := by decide

theorem tree : graph.IsTree := by
  apply isTree_iff_connected_and_card.mpr
  refine ⟨connected,?_⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← graph.edgeFinset_card, Fintype.card_fin]
  decide

theorem harmonic_exact : harmonicIndex graph = 24 / 5 := by
  unfold harmonicIndex
  have edges : graph.edgeFinset =
      {s(0,1), s(1,2), s(2,3), s(3,4), s(4,5), s(5,6), s(6,7), s(7,8), s(1,9), s(7,10)} := by
    decide
  rw [edges]
  simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton, Sym2.lift_mk]
  let deg (v : V) : ℕ := if v = 1 ∨ v = 7 then 3 else if 2 ≤ v ∧ v ≤ 6 then 2 else 1
  have degrees : ∀ v, graph.degree v = deg v := by decide
  simp only [degrees]
  simp (disch := decide) only [deg, if_pos, if_neg]
  norm_num

theorem ordered_sum_exact : orderedDistanceSum graph = 408 := by
  have h : graph.dist = distance := funext fun u => funext (metric.2 u)
  unfold orderedDistanceSum
  rw [h]
  decide

theorem mean_exact : averageShortestPathLength graph = 204 / 55 := by
  unfold averageShortestPathLength
  rw [ordered_sum_exact,Fintype.card_fin]
  norm_num

/-- Physical row 2598 on the numerical domain of its average-distance function. -/
theorem row2598_false : ¬ (∀ (U : Type) [Fintype U] [DecidableEq U]
    (G : SimpleGraph U) [DecidableRel G.Adj], 2 ≤ Fintype.card U →
    (∀ v, G.degree v ≤ 3) → G.Connected →
    averageShortestPathLength G ≤ (2/3 : ℚ) * harmonicIndex G + 1/2) := by
  intro claim
  have bound := claim V graph (by decide) subcubic connected
  rw [mean_exact,harmonic_exact] at bound
  norm_num at bound

#print axioms subcubic
#print axioms tree
#print axioms harmonic_exact
#print axioms ordered_sum_exact
#print axioms mean_exact
#print axioms row2598_false

end DoubleBroom2598
