import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum
import Mathlib.Data.Nat.Lattice
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lean.Elab.Tactic.Omega

/-! A connected triangle-free counterexample to AutoGraphForge physical row 362. -/
namespace BicliqueTail362
open SimpleGraph Finset

def Burns {U : Type*} (G : SimpleGraph U) (k : ℕ) : Prop :=
  ∃ source : Fin k → U, ∀ v, ∃ t : Fin k, ∃ p : G.Walk (source t) v,
    p.length ≤ k - 1 - t.val

noncomputable def burning {U : Type*} (G : SimpleGraph U) : ℕ := sInf {k | Burns G k}

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

abbrev V := Fin 17

/-- The path has levels 0 through 9. The seven last labels duplicate vertex 1. -/
def level (x : V) : ℕ := if x.val < 10 then x.val else 1

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

/-- Distinct vertices of level one have distance two via vertex zero. Elsewhere
different levels are connected by a monotone path. -/
def d (x y : V) : ℕ :=
  if x = y then 0 else if level x = level y then 2
  else max (level x) (level y) - min (level x) (level y)

theorem metric : (∀ x y, graph.Reachable x y) ∧ ∀ x y, graph.dist x y = d x y :=
  metric_certificate d (by decide) (by decide) (by decide)

theorem connected : graph.Connected := ⟨metric.1⟩

theorem subTotal_exact : subTotal? graph = some 2 := by
  let L := [9,8] ++ List.replicate 14 2 ++ [1]
  have degreeList : degreesDesc graph = L := by
    unfold degreesDesc
    rw [Finset.val_univ_fin, Multiset.map_coe, Multiset.coe_sort]
    have eq : (List.finRange 17).map (fun v => graph.degree v) =
        [8,2,9,2,2,2,2,2,2,1,2,2,2,2,2,2,2] := by decide
    rw [eq]
    simp [List.mergeSort,L]
  unfold subTotal?
  rw [degreeList]
  decide

/-- One representative of each level lies on the distinguished ten-vertex path. -/
def spine : Finset V := univ.filter (fun x => x.val < 10)
def spineBall (x : V) (r : ℕ) := spine.filter (fun w => d x w ≤ r)

theorem burns_lower {k : ℕ} (h : Burns graph k) : 4 ≤ k := by
  by_contra! small
  obtain ⟨source, cover⟩ := h
  let rad (i : Fin k) := k - 1 - i.val
  let balls (i : Fin k) := spineBall (source i) (rad i)
  have sub : spine ⊆ univ.biUnion balls := by
    intro w hw
    obtain ⟨i,p,hp⟩ := cover w
    exact mem_biUnion.mpr ⟨i,mem_univ _,mem_filter.mpr ⟨hw,(metric.2 _ _ ▸ dist_le p).trans hp⟩⟩
  have cap : ∀ x : V, ∀ r : Fin 3, (spineBall x r.val).card ≤ 2*r.val+1 := by decide
  have caps (i : Fin k) : (balls i).card ≤ 2*rad i+1 :=
    cap (source i) ⟨rad i,by dsimp [rad]; omega⟩
  have widths : ∀ n : Fin 4, (∑ i : Fin n.val, (2*(n.val-1-i.val)+1)) ≤ 9 := by decide
  have impossible : 10 ≤ 9 := calc
    10 = spine.card := by decide
    _ ≤ (univ.biUnion balls).card := card_le_card sub
    _ ≤ ∑ i : Fin k, (balls i).card := card_biUnion_le
    _ ≤ ∑ i : Fin k, (2*rad i+1) := sum_le_sum (fun i _ => caps i)
    _ ≤ 9 := widths ⟨k,small⟩
  omega

theorem burns_four : Burns graph 4 := by
  let source (i : Fin 4) : V := if i=0 then 0 else if i=1 then 4 else if i=2 then 7 else 9
  have cover : ∀ w : V, ∃ i : Fin 4, d (source i) w ≤ 4-1-i.val := by decide
  refine ⟨source,fun w => ?_⟩
  obtain ⟨i,hi⟩ := cover w
  obtain ⟨p,hp⟩ := (metric.1 (source i) w).exists_walk_length_eq_dist
  exact ⟨i,p,by rw [hp,metric.2]; exact hi⟩

theorem burning_exact : burning graph = 4 := by
  have h : 4 ∈ {k | Burns graph k} := burns_four
  exact le_antisymm (Nat.sInf_le h) (burns_lower (Nat.sInf_mem ⟨4,h⟩))

/-- Physical row 362, with the source routine restricted to its numerical domain. -/
theorem row362_false : ¬ (∀ (U : Type) [Fintype U] (G : SimpleGraph U) [DecidableRel G.Adj]
    (s : ℕ), 2 ≤ Fintype.card U → TriangleFree G → subTotal? G = some s →
    (burning G : ℚ) ≤ (3/2 : ℚ)*s) := by
  intro conjecture
  have bound := conjecture V graph 2 (by decide) triangle_free subTotal_exact
  rw [burning_exact] at bound
  norm_num at bound

#print axioms connected
#print axioms triangle_free
#print axioms subTotal_exact
#print axioms burning_exact
#print axioms row362_false

end BicliqueTail362
