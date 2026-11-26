import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
Lean 4.19 certificate of Jonas J. Gebendorfer's U_10 counterexample to WOW II #363.
The positive nearest-boundary average follows catalogue definition 109.
-/

namespace Graffiti363
open Finset SimpleGraph
open scoped BigOperators

section Definitions
variable {V : Type*} (G : SimpleGraph V)

def TotalDominates (D : Finset V) : Prop := ∀ v, ∃ w ∈ D, G.Adj v w

noncomputable def totalDominationNumber : ℕ :=
  sInf {k : ℕ | ∃ D, TotalDominates G D ∧ D.card = k}

noncomputable def distanceFrom (S : Finset V) (v : V) : ℕ :=
  sInf {k : ℕ | ∃ w ∈ S, G.dist w v = k}

theorem distanceFrom_pos_iff (hc : G.Connected) {S : Finset V} (hS : S.Nonempty) (v : V) :
    0 < distanceFrom G S v ↔ v ∉ S := by
  constructor
  · intro hp hv
    have hl : distanceFrom G S v ≤ 0 :=
      Nat.sInf_le ⟨v,hv,G.dist_self⟩
    omega
  · intro hv
    obtain ⟨s,hs⟩ := hS
    have hne : {k : ℕ | ∃ w ∈ S, G.dist w v = k}.Nonempty :=
      ⟨G.dist s v,s,hs,rfl⟩
    obtain ⟨w,hw,hval⟩ := Nat.sInf_mem hne
    rw [distanceFrom, ← hval]
    exact hc.pos_dist_of_ne (fun h => hv (h ▸ hw))

variable [Fintype V]

noncomputable def eccentricity (v : V) : ℕ := univ.sup (G.dist v)

noncomputable def boundary : Finset V :=
  @Finset.filter V (fun v => ∀ w, eccentricity G w ≤ eccentricity G v)
    (fun _ => Classical.propDecidable _) univ

theorem mem_boundary {v : V} :
    v ∈ boundary G ↔ ∀ w, eccentricity G w ≤ eccentricity G v := by
  unfold boundary
  exact (@Finset.mem_filter V _ (fun _ => Classical.propDecidable _) univ v).trans
    ⟨And.right,fun h => ⟨mem_univ v,h⟩⟩

noncomputable def positiveTerms : Finset V :=
  univ.filter (fun v => 0 < distanceFrom G (boundary G) v)

theorem positiveTerms_eq_sdiff [DecidableEq V] (hc : G.Connected) (hB : (boundary G).Nonempty) :
    positiveTerms G = univ \ boundary G := by
  ext v
  simp [positiveTerms, distanceFrom_pos_iff G hc hB]

/-- Catalogue definition 109, with a rational mean over positive distances only. -/
noncomputable def meanPositiveBoundaryDistance : ℚ :=
  ((∑ v ∈ positiveTerms G, distanceFrom G (boundary G) v : ℕ) : ℚ) /
    ((positiveTerms G).card : ℚ)

variable [DecidableRel G.Adj]

def supportVertices : Finset V :=
  univ.filter (fun v => ∃ w, G.Adj v w ∧ G.degree w = 1)

def isolatedSupports : Finset V :=
  (supportVertices G).filter (fun v => ∀ w ∈ supportVertices G, ¬G.Adj v w)

/-- The isolates here are taken in the graph induced by the support vertices. -/
theorem mem_isolatedSupports_iff (v : supportVertices G) :
    (v : V) ∈ isolatedSupports G ↔
      (G.induce (supportVertices G : Set V)).neighborSet v = ∅ := by
  simp only [isolatedSupports,mem_filter, v.property, true_and]
  constructor
  · intro h
    apply Set.eq_empty_iff_forall_not_mem.mpr
    intro w hw
    exact h w w.property hw
  · intro h w hw ha
    have hm : (⟨w,hw⟩ : supportVertices G) ∈
        (G.induce (supportVertices G : Set V)).neighborSet v := ha
    rw [h] at hm
    exact hm

end Definitions

abbrev Vertex := Fin 27

/-- 0 is h, 1–5 are a1–a5, 6 is x, 7–11 are b1–b5, 12 is y,
13–16 are r,t,z,u, and 17–26 are the ten leaves at z. -/
def parent (v : Vertex) : Vertex :=
  ![0,0,1,2,3,4,2,0,7,8,9,10,8,0,13,14,13,15,15,15,15,15,15,15,15,15,15] v

def witness : SimpleGraph Vertex where
  Adj u v := u ≠ v ∧ (parent u = v ∨ parent v = u)
  symm _ _ h := ⟨h.1.symm,h.2.symm⟩
  loopless _ h := h.1 rfl

instance : DecidableRel witness.Adj :=
  inferInstanceAs (DecidableRel (fun u v : Vertex => u ≠ v ∧ (parent u = v ∨ parent v = u)))

private def up (next : Vertex → Vertex) : ℕ → Vertex → Vertex
  | 0, v => v
  | k + 1, v => up next k (next v)

private theorem upWalk {next : Vertex → Vertex} {r : Vertex}
    (hEdge : ∀ v, v ≠ r → witness.Adj v (next v)) (k : ℕ) (v : Vertex)
    (h : up next k v = r) : ∃ p : witness.Walk v r, p.length ≤ k := by
  induction k generalizing v with
  | zero =>
    change v = r at h
    subst v
    exact ⟨.nil,by simp⟩
  | succ k ih =>
    by_cases hv : v = r
    · subst v
      exact ⟨.nil,by simp⟩
    · obtain ⟨p,hp⟩ := ih (next v) h
      exact ⟨.cons (hEdge v hv) p,by simpa⟩

private def depth (v : Vertex) : ℕ :=
  ![0,1,2,3,4,5,3,1,2,3,4,5,3,1,2,3,2,4,4,4,4,4,4,4,4,4,4] v

private theorem depthRoute : ∀ v : Vertex, up parent (depth v) v = 0 := by decide

private theorem parent_adj : ∀ v : Vertex, v ≠ 0 → witness.Adj v (parent v) := by decide

theorem witness_connected : witness.Connected := by
  apply (connected_iff_exists_forall_reachable witness).mpr
  refine ⟨0,fun v => ?_⟩
  obtain ⟨p,_⟩ := upWalk parent_adj (depth v) v (depthRoute v)
  exact ⟨p.reverse⟩

theorem witness_order : Fintype.card Vertex = 27 := by decide

set_option maxHeartbeats 5000000 in
private theorem degree_sum : ∑ v : Vertex, witness.degree v = 52 := by decide

theorem witness_tree : witness.IsTree := by
  apply isTree_iff_connected_and_card.mpr
  refine ⟨witness_connected,?_⟩
  classical
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← edgeFinset_card, witness_order]
  have hsum := witness.sum_degrees_eq_twice_card_edges
  have he : (∑ v : Vertex, witness.degree v) = 52 := degree_sum
  rw [he] at hsum
  omega

private theorem dist_to_h_le_depth (v : Vertex) : witness.dist v 0 ≤ depth v := by
  obtain ⟨p,hp⟩ := upWalk parent_adj (depth v) v (depthRoute v)
  exact (witness.dist_le p).trans hp

private theorem dist_le_depth_sum (u v : Vertex) : witness.dist u v ≤ depth u + depth v := by
  have h : witness.dist u v ≤ witness.dist u 0 + witness.dist 0 v :=
    witness_connected.dist_triangle
  rw [witness.dist_comm (u := 0) (v := v)] at h
  exact h.trans (Nat.add_le_add (dist_to_h_le_depth u) (dist_to_h_le_depth v))

def distanceLabelA (v : Vertex) : ℕ :=
  ![5,4,3,2,1,0,4,6,7,8,9,10,8,6,7,8,7,9,9,9,9,9,9,9,9,9,9] v

def distanceLabelB (v : Vertex) : ℕ :=
  ![5,6,7,8,9,10,8,4,3,2,1,0,4,6,7,8,7,9,9,9,9,9,9,9,9,9,9] v

private def towardA (v : Vertex) : Vertex :=
  if v.val < 5 then v + 1 else if v = 5 then v else parent v

private def towardB (v : Vertex) : Vertex :=
  if v = 0 then 7 else if 7 ≤ v.val ∧ v.val < 11 then v + 1
  else if v = 11 then v else parent v

private theorem label_lipschitz_of_parent {f : Vertex → ℕ}
    (hf : ∀ v, f v ≤ f (parent v) + 1 ∧ f (parent v) ≤ f v + 1) :
    ∀ u v, witness.Adj u v → f u ≤ f v + 1 := by
  intro u v h
  obtain he | he := h.2
  · simpa only [he] using (hf u).1
  · simpa only [he] using (hf v).2

private theorem label_le_of_walk {f : Vertex → ℕ}
    (h : ∀ u v, witness.Adj u v → f u ≤ f v + 1) {u v : Vertex} (p : witness.Walk u v) :
    f u ≤ f v + p.length := by
  induction p with
  | nil => simp
  | @cons a b c he p ih =>
    have hl := h a b he
    simp only [Walk.length_cons]
    omega

private theorem dist_from_label {f : Vertex → ℕ} {next : Vertex → Vertex} {r : Vertex}
    (hzero : f r = 0) (hroute : ∀ v, up next (f v) v = r)
    (hedge : ∀ v, v ≠ r → witness.Adj v (next v))
    (hlip : ∀ v, f v ≤ f (parent v) + 1 ∧ f (parent v) ≤ f v + 1) (v : Vertex) :
    witness.dist r v = f v := by
  apply le_antisymm
  · obtain ⟨p,hp⟩ := upWalk hedge (f v) v (hroute v)
    exact (witness.dist_le p.reverse).trans (by simpa using hp)
  · obtain ⟨p,hp⟩ := witness_connected.exists_walk_length_eq_dist v r
    have h := label_le_of_walk (label_lipschitz_of_parent hlip) p
    simpa [hzero,hp,witness.dist_comm (u := v) (v := r)] using h

theorem distA (v : Vertex) : witness.dist 5 v = distanceLabelA v := by
  apply dist_from_label (next := towardA) (v := v) <;> decide

theorem distB (v : Vertex) : witness.dist 11 v = distanceLabelB v := by
  apply dist_from_label (next := towardB) (v := v) <;> decide

private theorem pole_dist : witness.dist 5 11 = 10 := distA 11

private theorem ecc_le_depth_add_five (v : Vertex) :
    eccentricity witness v ≤ depth v + 5 := by
  have hd : ∀ w : Vertex, depth w ≤ 5 := by decide
  apply Finset.sup_le
  intro w _
  exact (dist_le_depth_sum v w).trans (Nat.add_le_add_left (hd w) _)

theorem boundary_eq : boundary witness = {5,11} := by
  have h5 : 10 ≤ eccentricity witness 5 := pole_dist ▸ le_sup (f := witness.dist 5) (mem_univ 11)
  have h11 : 10 ≤ eccentricity witness 11 := by
    have h := le_sup (f := witness.dist 11) (mem_univ 5)
    rw [witness.dist_comm (u := 11) (v := 5),pole_dist] at h
    exact h
  have hd : ∀ v : Vertex, v ≠ 5 → v ≠ 11 → depth v ≤ 4 := by decide
  have hmax : ∀ v : Vertex, eccentricity witness v ≤ 10 := by
    have hdepth : ∀ v : Vertex, depth v ≤ 5 := by decide
    intro v
    exact (ecc_le_depth_add_five v).trans (Nat.add_le_add_right (hdepth v) 5)
  ext v
  simp only [mem_boundary,mem_insert,mem_singleton]
  constructor
  · intro hv
    by_contra h
    have hsmall := hd v (fun h' => h (Or.inl h')) (fun h' => h (Or.inr h'))
    have he := ecc_le_depth_add_five v
    have hbig := h5.trans (hv 5)
    omega
  · rintro (rfl | rfl) w
    · exact (hmax w).trans h5
    · exact (hmax w).trans h11

private def candidateLeaves : Finset Vertex := {5,6,11,12,16,17,18,19,20,21,22,23,24,25,26}

set_option maxHeartbeats 5000000 in
private theorem leaves_exact : ∀ v : Vertex, witness.degree v = 1 ↔ v ∈ candidateLeaves := by decide

def candidateSupports : Finset Vertex := {2,4,8,10,13,15}

set_option maxHeartbeats 5000000 in
private theorem supports_check :
    ∀ v : Vertex, (∃ w, witness.Adj v w ∧ w ∈ candidateLeaves) ↔
      v ∈ candidateSupports := by decide

theorem support_eq : supportVertices witness = candidateSupports := by
  ext v
  simp only [supportVertices,mem_filter,mem_univ,true_and,leaves_exact]
  exact supports_check v

set_option maxHeartbeats 5000000 in
private theorem support_independent :
    ∀ v w : Vertex, v ∈ candidateSupports → w ∈ candidateSupports → ¬witness.Adj v w := by decide

theorem isolatedSupports_card : (isolatedSupports witness).card = 6 := by
  have he : isolatedSupports witness = candidateSupports := by
    ext v
    simp only [isolatedSupports, support_eq, mem_filter]
    exact ⟨And.left,fun h => ⟨h,fun w hw => support_independent v w h hw⟩⟩
  rw [he]
  decide

private def nearest (v : Vertex) : ℕ := min (distanceLabelA v) (distanceLabelB v)

theorem distanceFrom_boundary_eq (v : Vertex) :
    distanceFrom witness (boundary witness) v = nearest v := by
  rw [boundary_eq]
  let B : Finset Vertex := {5,11}
  change distanceFrom witness B v = nearest v
  have h5 : (5 : Vertex) ∈ B := by decide
  have h11 : (11 : Vertex) ∈ B := by decide
  apply le_antisymm
  · have hA : distanceFrom witness B v ≤ distanceLabelA v := Nat.sInf_le ⟨5,h5,distA v⟩
    have hB : distanceFrom witness B v ≤ distanceLabelB v := Nat.sInf_le ⟨11,h11,distB v⟩
    exact le_min hA hB
  · have hne : {k : ℕ | ∃ w ∈ B, witness.dist w v = k}.Nonempty :=
      ⟨distanceLabelA v,5,h5,distA v⟩
    obtain ⟨w,hw,he⟩ := Nat.sInf_mem hne
    rw [distanceFrom, ← he]
    change w ∈ ({5,11} : Finset Vertex) at hw
    simp only [mem_insert,mem_singleton] at hw
    obtain rfl | rfl := hw
    · rw [distA]
      exact min_le_left _ _
    · rw [distB]
      exact min_le_right _ _

theorem positiveTerms_eq : positiveTerms witness = univ \ {5,11} := by
  have hb : (boundary witness).Nonempty := by rw [boundary_eq]; decide
  rw [positiveTerms_eq_sdiff witness witness_connected hb, boundary_eq]

theorem nearest_positive_sum :
    ∑ v ∈ positiveTerms witness, distanceFrom witness (boundary witness) v = 151 := by
  simp_rw [distanceFrom_boundary_eq]
  rw [positiveTerms_eq]
  decide

theorem positiveTerms_card : (positiveTerms witness).card = 25 := by
  rw [positiveTerms_eq]
  decide

theorem boundaryAverage_eq : meanPositiveBoundaryDistance witness = (151 : ℚ) / 25 := by
  rw [meanPositiveBoundaryDistance, nearest_positive_sum, positiveTerms_card]
  norm_num

def selected : Finset Vertex := {2,3,4,8,9,10,13,14,15}

theorem selected_total : TotalDominates witness selected := by
  unfold TotalDominates
  decide

private def packing (i : Fin 9) : Vertex := ![1,4,5,12,10,11,0,15,17] i

set_option maxHeartbeats 5000000 in
private theorem packing_neighbor_unique :
    ∀ v : Vertex, (univ.filter (fun i : Fin 9 => witness.Adj (packing i) v)).card ≤ 1 := by decide

theorem totalDomination_eq : totalDominationNumber witness = 9 := by
  apply le_antisymm
  · exact Nat.sInf_le ⟨selected,selected_total,by decide⟩
  · have hn : {k : ℕ | ∃ D, TotalDominates witness D ∧ D.card = k}.Nonempty :=
      ⟨9,selected,selected_total,by decide⟩
    obtain ⟨D,hD,hcard⟩ := Nat.sInf_mem hn
    change 9 ≤ sInf _
    rw [← hcard]
    choose f hf ha using fun i : Fin 9 => hD (packing i)
    let e (i : Fin 9) : D := ⟨f i,hf i⟩
    have he : Function.Injective e := by
      intro i j h
      have heq : f i = f j := congrArg Subtype.val h
      have hi : i ∈ univ.filter (fun k : Fin 9 => witness.Adj (packing k) (f i)) :=
        mem_filter.mpr ⟨mem_univ _,ha i⟩
      have hj : j ∈ univ.filter (fun k : Fin 9 => witness.Adj (packing k) (f i)) :=
        mem_filter.mpr ⟨mem_univ _,heq ▸ ha j⟩
      by_contra hne
      have hl := card_le_card (show {i,j} ⊆ _ from insert_subset hi (singleton_subset_iff.mpr hj))
      rw [card_pair hne] at hl
      exact (by decide : ¬ 2 ≤ 1) (hl.trans (packing_neighbor_unique (f i)))
    simpa using Fintype.card_le_of_injective e he

theorem counterexample363 :
    witness.IsTree ∧ 2 < Fintype.card Vertex ∧
      (totalDominationNumber witness : ℚ) <
        ((isolatedSupports witness).card : ℚ) +
          (1 / 2 : ℚ) * meanPositiveBoundaryDistance witness := by
  refine ⟨witness_tree,by decide,?_⟩
  rw [totalDomination_eq, isolatedSupports_card, boundaryAverage_eq]
  norm_num

theorem conjecture363_false :
    ¬ ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
      G.IsTree → 2 < Fintype.card V →
        ((isolatedSupports G).card : ℚ) + (1 / 2 : ℚ) * meanPositiveBoundaryDistance G ≤
          (totalDominationNumber G : ℚ) := by
  intro h
  exact (not_le_of_gt counterexample363.2.2) (h Vertex witness witness_tree (by decide))

#print axioms distanceFrom_pos_iff
#print axioms boundary_eq
#print axioms isolatedSupports_card
#print axioms boundaryAverage_eq
#print axioms totalDomination_eq
#print axioms conjecture363_false

end Graffiti363
