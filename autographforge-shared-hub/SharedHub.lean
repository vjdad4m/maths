import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum
import Mathlib.Data.Nat.Lattice
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lean.Elab.Tactic.Omega

/-! A common counterexample to AutoGraphForge normalized rows 747, 1889, 2517.
Burning and Slater definitions are from the published row 33 proof. The metric
certificate, diameter and Eulerian definitions are from the row 501/764 proof. -/

namespace SharedHub

open SimpleGraph Finset

def Burns {U : Type*} (G : SimpleGraph U) (k : ℕ) : Prop :=
  ∃ source : Fin k → U, ∀ v, ∃ t : Fin k, ∃ p : G.Walk (source t) v,
    p.length ≤ k - 1 - t.val

noncomputable def burning {U : Type*} (G : SimpleGraph U) : ℕ := sInf {k | Burns G k}

noncomputable def degreesDesc {U : Type*} [Fintype U] (G : SimpleGraph U) [DecidableRel G.Adj] :=
  (univ.val.map (fun v => G.degree v)).sort (· ≥ ·)

noncomputable def slater {U : Type*} [Fintype U] (G : SimpleGraph U) [DecidableRel G.Adj] :=
  sInf {t | Fintype.card U ≤ t + ((degreesDesc G).take t).sum}

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

noncomputable def eccentricity {U : Type*} [Fintype U] (G : SimpleGraph U) (u : U) := univ.sup (G.dist u)
noncomputable def diameter {U : Type*} [Fintype U] (G : SimpleGraph U) := univ.sup (eccentricity G)

/-- AutoGraphForge's separate diameter wrapper represents an undefined value by infinity. -/
noncomputable def sourceDiameter {U : Type*} [Fintype U] (G : SimpleGraph U) : WithTop ℚ := by
  classical
  exact if G.Connected then ((diameter G : ℚ) : WithTop ℚ) else ⊤

/-- The Euler criterion used by NetworkX for the undirected connected case. -/
def Eulerian {U : Type*} [Fintype U] (G : SimpleGraph U) [DecidableRel G.Adj] : Prop :=
  G.Connected ∧ ∀ u, G.degree u % 2 = 0

abbrev V := Fin 23

/-- Labels 0 through 11 form the cycle. The two hubs are 0 and 12. -/
def edgeB (x y : V) : Bool :=
  ((x.val < 12 && y.val < 12) &&
    (x.val + 1 == y.val || y.val + 1 == x.val ||
     (x.val == 0 && y.val == 11) || (x.val == 11 && y.val == 0))) ||
  ((x.val == 0 || x.val == 12) && 13 ≤ y.val) ||
  ((y.val == 0 || y.val == 12) && 13 ≤ x.val)

def graph : SimpleGraph V where
  Adj x y := edgeB x y = true
  symm := by
    have h : ∀ x y : V, edgeB x y = true → edgeB y x = true := by decide
    exact fun x y => h x y
  loopless := by
    have h : ∀ x : V, edgeB x x ≠ true := by decide
    exact h

instance : DecidableRel graph.Adj := fun x y => inferInstanceAs (Decidable (edgeB x y = true))

/-- Shorter arc length on the cycle. -/
def arc (x y : ℕ) : ℕ :=
  let gap := max x y - min x y
  min gap (12 - gap)

def depth (x : V) : ℕ := if x = 12 then 2 else 1

def d (x y : V) : ℕ :=
  if x = y then 0
  else if x.val < 12 then
    if y.val < 12 then arc x.val y.val else arc x.val 0 + depth y
  else if y.val < 12 then depth x + arc 0 y.val
  else if x = 12 ∨ y = 12 then 1 else 2

set_option maxRecDepth 10000
set_option maxHeartbeats 6000000

theorem metric : (∀ x y, graph.Reachable x y) ∧ ∀ x y, graph.dist x y = d x y :=
  metric_certificate d (by decide) (by decide) (by decide)

theorem connected : graph.Connected := ⟨metric.1⟩

theorem eulerian : Eulerian graph := ⟨connected, by decide⟩

def TriangleFree {U : Type*} (G : SimpleGraph U) : Prop :=
  ∀ x y z, G.Adj x y → G.Adj y z → ¬ G.Adj z x

theorem triangle_free : TriangleFree graph := by unfold TriangleFree; decide

theorem slater_exact : slater graph = 2 := by
  let L : List ℕ := [12,10] ++ List.replicate 21 2
  have degreeList : degreesDesc graph = L := by
    unfold degreesDesc
    rw [Finset.val_univ_fin, Multiset.map_coe, Multiset.coe_sort]
    have eq : (List.finRange 23).map (fun v => graph.degree v) =
        [12,2,2,2,2,2,2,2,2,2,2,2,10,2,2,2,2,2,2,2,2,2,2] := by decide
    rw [eq]
    simp [List.mergeSort,L]
  unfold slater
  rw [degreeList,Fintype.card_fin]
  let costs : Set ℕ := {k | 23 ≤ k + (L.take k).sum}
  have feasible : 2 ∈ costs := by decide
  apply Nat.le_antisymm (Nat.sInf_le (s := costs) feasible)
  have good := Nat.sInf_mem (show costs.Nonempty from ⟨_,feasible⟩)
  change 2 ≤ sInf costs
  by_cases hi : 2 ≤ sInf costs
  · exact hi
  exfalso
  obtain h | h := (show sInf costs=0 ∨ sInf costs=1 by omega)
  · rw [h] at good
    exact (show 0 ∉ costs by decide) good
  · rw [h] at good
    exact (show 1 ∉ costs by decide) good

theorem diameter_exact : diameter graph = 8 := by
  have eq : graph.dist = d := funext (fun x => funext (metric.2 x))
  unfold diameter eccentricity
  rw [eq]
  decide

def cycleVertices : Finset V := univ.filter (fun x => x.val < 12)
def cycleBall (v : V) (r : ℕ) : Finset V := cycleVertices.filter (fun w => d v w ≤ r)

/-- A ball of any radius about any vertex meets the cycle in at most 2r+1 vertices.
For r < 6 this checks the cycle distance formula. At larger radii, 12 suffices. -/
theorem ball_capacity (v : V) (r : ℕ) : (cycleBall v r).card ≤ 2*r+1 := by
  by_cases small : r < 6
  · have check : ∀ x : V, ∀ i : Fin 6, (cycleBall x i.val).card ≤ 2*i.val+1 := by decide
    exact check v ⟨r,small⟩
  · have bound := card_le_card (filter_subset (fun w => d v w ≤ r) cycleVertices)
    have size : cycleVertices.card = 12 := by decide
    change (cycleBall v r).card ≤ cycleVertices.card at bound
    omega

theorem burns_lower {k : ℕ} (h : Burns graph k) : 4 ≤ k := by
  by_contra! small
  obtain ⟨source, cover⟩ := h
  let rad (i : Fin k) := k - 1 - i.val
  let balls (i : Fin k) := cycleBall (source i) (rad i)
  have sub : cycleVertices ⊆ univ.biUnion balls := by
    intro w hw
    obtain ⟨i,p,hp⟩ := cover w
    refine mem_biUnion.mpr ⟨i,mem_univ _,mem_filter.mpr ⟨hw,?_⟩⟩
    exact (metric.2 _ _ ▸ dist_le p).trans hp
  have caps (i : Fin k) : (balls i).card ≤ 2*rad i + 1 :=
    ball_capacity (source i) (rad i)
  have h12 : cycleVertices.card = 12 := by decide
  have widths : ∀ n : Fin 4, (∑ i : Fin n.val, (2*(n.val-1-i.val)+1)) ≤ 9 := by decide
  have absurdBound : 12 ≤ 9 := calc
    12 = cycleVertices.card := h12.symm
    _ ≤ (univ.biUnion balls).card := card_le_card sub
    _ ≤ ∑ i : Fin k, (balls i).card := card_biUnion_le
    _ ≤ ∑ i : Fin k, (2*rad i+1) := sum_le_sum (fun i _ => caps i)
    _ ≤ 9 := widths ⟨k,small⟩
  omega

theorem burns_four : Burns graph 4 := by
  let schedule (t : Fin 4) : V := if t = 0 then 0 else if t = 1 then 6 else if t = 2 then 3 else 9
  have cover : ∀ w : V, ∃ t : Fin 4, d (schedule t) w ≤ 4-1-t.val := by decide
  refine ⟨schedule,fun w => ?_⟩
  obtain ⟨t,ht⟩ := cover w
  obtain ⟨p,hp⟩ := (metric.1 (schedule t) w).exists_walk_length_eq_dist
  exact ⟨t,p,by rw [hp,metric.2]; exact ht⟩

theorem burning_exact : burning graph = 4 := by
  have h : 4 ∈ {k | Burns graph k} := burns_four
  exact le_antisymm (Nat.sInf_le h) (burns_lower (Nat.sInf_mem ⟨4,h⟩))

theorem row747_false : ¬ (∀ (U : Type) [Fintype U] (G : SimpleGraph U) [DecidableRel G.Adj],
    2 ≤ Fintype.card U → Eulerian G → TriangleFree G →
      (burning G : ℚ) ≤ (3/2 : ℚ) * slater G) := by
  intro claim
  have h := claim V graph (by decide) eulerian triangle_free
  rw [burning_exact,slater_exact] at h
  norm_num at h

theorem row1889_false : ¬ (∀ (U : Type) [Fintype U] (G : SimpleGraph U) [DecidableRel G.Adj],
    2 ≤ Fintype.card U → Eulerian G → TriangleFree G →
      (burning G : ℚ) ≤ (1/3 : ℚ) * slater G + 3) := by
  intro claim
  have h := claim V graph (by decide) eulerian triangle_free
  rw [burning_exact,slater_exact] at h
  norm_num at h

/-- Even restricting the diameter inequality to connected inputs gives a contradiction. -/
theorem row2517_connected_false : ¬ (∀ (U : Type) [Fintype U] (G : SimpleGraph U) [DecidableRel G.Adj],
    2 ≤ Fintype.card U → G.Connected →
      (diameter G : ℚ) ≤ (14/5 : ℚ) * slater G + 7/5) := by
  intro claim
  have h := claim V graph (by decide) connected
  rw [diameter_exact,slater_exact] at h
  norm_num at h

/-- Physical row 2517 has only the order hypothesis. Specialization to the connected
domain coincides with GraphCalc's finite-valued diameter test. -/
theorem row2517_false : ¬ (∀ (U : Type) [Fintype U] (G : SimpleGraph U) [DecidableRel G.Adj],
    2 ≤ Fintype.card U →
      sourceDiameter G ≤ (((14/5 : ℚ) * slater G + 7/5 : ℚ) : WithTop ℚ)) := by
  intro claim
  apply row2517_connected_false
  intro U _ G _ hn hc
  simpa only [sourceDiameter, if_pos hc, WithTop.coe_le_coe] using claim U G hn

#print axioms burning_exact
#print axioms diameter_exact
#print axioms slater_exact
#print axioms row747_false
#print axioms row1889_false
#print axioms row2517_false

end SharedHub
