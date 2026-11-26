import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# A coefficient-1/3 counterexample to a strengthened form of WOW II #363

The catalogue uses 1/2. Gebendorfer's October 2026 example refuted that
coefficient and left 1/3 open. Here we verify a finite counterexample
even at 1/3, against the mean of positive distances to the periphery
(catalogue definition 109).

Take a root with two length-seven arms and one length-six arm. On
the first two arms attach private leaves at positions one and four.
On the third arm attach private leaves at positions one, three and
five, then attach 147 further leaves at position five. The two long
tips are the periphery; the isolated-support count is nine.
A size-13 total dominating set is exhibited. The distance mean is
2065/172, so the proposed lower bound is 13+1/516.
-/

namespace Graffiti363Strong
set_option maxRecDepth 12000
set_option maxHeartbeats 30000000
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

abbrev Vertex := Fin 174

def parent (v : Vertex) : Vertex :=
  if h : v.val < 27 then
    (![ 0,0,1,2,3,4,5,6,4,1,0,10,11,12,13,14,15,13,10,0,19,20,21,22,23,19,21 ] : Fin 27 → Vertex) ⟨v.val,h⟩
  else 23

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
  if h : v.val < 27 then
    (![ 0,1,2,3,4,5,6,7,5,2,1,2,3,4,5,6,7,5,2,1,2,3,4,5,6,2,4 ] : Fin 27 → ℕ) ⟨v.val,h⟩
  else 6

private theorem depthRoute : ∀ v : Vertex, up parent (depth v) v = 0 := by decide

private theorem parent_adj : ∀ v : Vertex, v ≠ 0 → witness.Adj v (parent v) := by decide

theorem witness_connected : witness.Connected := by
  apply (connected_iff_exists_forall_reachable witness).mpr
  refine ⟨0,fun v => ?_⟩
  obtain ⟨p,_⟩ := upWalk parent_adj (depth v) v (depthRoute v)
  exact ⟨p.reverse⟩

theorem witness_order : Fintype.card Vertex = 174 := by decide

set_option maxHeartbeats 30000000 in
private theorem degree_sum : ∑ v : Vertex, witness.degree v = 346 := by decide

theorem witness_tree : witness.IsTree := by
  apply isTree_iff_connected_and_card.mpr
  refine ⟨witness_connected,?_⟩
  classical
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← edgeFinset_card, witness_order]
  have hsum := witness.sum_degrees_eq_twice_card_edges
  have he : (∑ v : Vertex, witness.degree v) = 346 := degree_sum
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
  if h : v.val < 27 then
    (![ 7,6,5,4,3,2,1,0,4,7,8,9,10,11,12,13,14,12,9,8,9,10,11,12,13,9,11 ] : Fin 27 → ℕ) ⟨v.val,h⟩
  else 13
def distanceLabelB (v : Vertex) : ℕ :=
  if h : v.val < 27 then
    (![ 7,8,9,10,11,12,13,14,12,9,6,5,4,3,2,1,0,4,7,8,9,10,11,12,13,9,11 ] : Fin 27 → ℕ) ⟨v.val,h⟩
  else 13
private def towardA (v : Vertex) : Vertex :=
  if h : v.val < 27 then
    (![ 1,2,3,4,5,6,7,7,4,1,0,10,11,12,13,14,15,13,10,0,19,20,21,22,23,19,21 ] : Fin 27 → Vertex) ⟨v.val,h⟩
  else 23
private def towardB (v : Vertex) : Vertex :=
  if h : v.val < 27 then
    (![ 10,0,1,2,3,4,5,6,4,1,11,12,13,14,15,16,16,13,10,0,19,20,21,22,23,19,21 ] : Fin 27 → Vertex) ⟨v.val,h⟩
  else 23

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

theorem distA (v : Vertex) : witness.dist 7 v = distanceLabelA v := by
  apply dist_from_label (next := towardA) (v := v) <;> decide

theorem distB (v : Vertex) : witness.dist 16 v = distanceLabelB v := by
  apply dist_from_label (next := towardB) (v := v) <;> decide

private theorem pole_dist : witness.dist 7 16 = 14 := distA 16

private theorem ecc_le_depth_add_seven (v : Vertex) :
    eccentricity witness v ≤ depth v + 7 := by
  have hd : ∀ w : Vertex, depth w ≤ 7 := by decide
  apply Finset.sup_le
  intro w _
  exact (dist_le_depth_sum v w).trans (Nat.add_le_add_left (hd w) _)

theorem boundary_eq : boundary witness = {7,16} := by
  have h5 : 14 ≤ eccentricity witness 7 := pole_dist ▸ le_sup (f := witness.dist 7) (mem_univ 16)
  have h11 : 14 ≤ eccentricity witness 16 := by
    have h := le_sup (f := witness.dist 16) (mem_univ 7)
    rw [witness.dist_comm (u := 16) (v := 7),pole_dist] at h
    exact h
  have hd : ∀ v : Vertex, v ≠ 7 → v ≠ 16 → depth v ≤ 6 := by decide
  have hmax : ∀ v : Vertex, eccentricity witness v ≤ 14 := by
    have hdepth : ∀ v : Vertex, depth v ≤ 7 := by decide
    intro v
    exact (ecc_le_depth_add_seven v).trans (Nat.add_le_add_right (hdepth v) 7)
  ext v
  simp only [mem_boundary,mem_insert,mem_singleton]
  constructor
  · intro hv
    by_cases h : v = 7 ∨ v = 16
    · exact h
    exfalso
    have hsmall := hd v (fun h' => h (Or.inl h')) (fun h' => h (Or.inr h'))
    have he := ecc_le_depth_add_seven v
    have hbig := h5.trans (hv 7)
    omega
  · rintro (rfl | rfl) w
    · exact (hmax w).trans h5
    · exact (hmax w).trans h11

private def candidateLeaves : Finset Vertex :=
  univ.filter (fun v => v.val ≥ 27 ∨ v ∈ ({7,8,9,16,17,18,24,25,26} : Finset Vertex))

set_option maxHeartbeats 30000000 in
private theorem leaves_exact : ∀ v : Vertex, witness.degree v = 1 ↔ v ∈ candidateLeaves := by decide

def candidateSupports : Finset Vertex := {1,4,6,10,13,15,19,21,23}

set_option maxHeartbeats 30000000 in
private theorem supports_check :
    ∀ v : Vertex, (∃ w, witness.Adj v w ∧ w ∈ candidateLeaves) ↔
      v ∈ candidateSupports := by decide

theorem support_eq : supportVertices witness = candidateSupports := by
  ext v
  simp only [supportVertices,mem_filter,mem_univ,true_and,leaves_exact]
  exact supports_check v

set_option maxHeartbeats 30000000 in
private theorem support_independent :
    ∀ v w : Vertex, v ∈ candidateSupports → w ∈ candidateSupports → ¬witness.Adj v w := by decide

theorem isolatedSupports_card : (isolatedSupports witness).card = 9 := by
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
  let B : Finset Vertex := {7,16}
  change distanceFrom witness B v = nearest v
  have h5 : (7 : Vertex) ∈ B := by decide
  have h11 : (16 : Vertex) ∈ B := by decide
  apply le_antisymm
  · have hA : distanceFrom witness B v ≤ distanceLabelA v := Nat.sInf_le ⟨7,h5,distA v⟩
    have hB : distanceFrom witness B v ≤ distanceLabelB v := Nat.sInf_le ⟨16,h11,distB v⟩
    exact le_min hA hB
  · have hne : {k : ℕ | ∃ w ∈ B, witness.dist w v = k}.Nonempty :=
      ⟨distanceLabelA v,7,h5,distA v⟩
    obtain ⟨w,hw,he⟩ := Nat.sInf_mem hne
    rw [distanceFrom, ← he]
    change w ∈ ({7,16} : Finset Vertex) at hw
    simp only [mem_insert,mem_singleton] at hw
    obtain rfl | rfl := hw
    · rw [distA]
      exact min_le_left _ _
    · rw [distB]
      exact min_le_right _ _

theorem positiveTerms_eq : positiveTerms witness = univ \ {7,16} := by
  have hb : (boundary witness).Nonempty := by rw [boundary_eq]; decide
  rw [positiveTerms_eq_sdiff witness witness_connected hb, boundary_eq]

theorem nearest_positive_sum :
    ∑ v ∈ positiveTerms witness, distanceFrom witness (boundary witness) v = 2065 := by
  simp_rw [distanceFrom_boundary_eq]
  rw [positiveTerms_eq]
  decide

theorem positiveTerms_card : (positiveTerms witness).card = 172 := by
  rw [positiveTerms_eq]
  decide

theorem boundaryAverage_eq : meanPositiveBoundaryDistance witness = (2065 : ℚ) / 172 := by
  rw [meanPositiveBoundaryDistance, nearest_positive_sum, positiveTerms_card]
  norm_num

def selected : Finset Vertex := {0,1,4,5,6,10,13,14,15,19,21,22,23}

theorem selected_total : TotalDominates witness selected := by
  unfold TotalDominates
  decide

theorem totalDomination_le : totalDominationNumber witness ≤ 13 :=
  Nat.sInf_le ⟨selected,selected_total,by decide⟩

/-- The 174-vertex witness refutes a coefficient of 1/3. -/
theorem counterexample_one_third :
    witness.IsTree ∧ 2 < Fintype.card Vertex ∧
      (totalDominationNumber witness : ℚ) <
        ((isolatedSupports witness).card : ℚ) +
          (1 / 3 : ℚ) * meanPositiveBoundaryDistance witness := by
  refine ⟨witness_tree,by decide,?_⟩
  rw [isolatedSupports_card,boundaryAverage_eq]
  have h : (totalDominationNumber witness : ℚ) ≤ 13 := by exact_mod_cast totalDomination_le
  exact lt_of_le_of_lt h (by norm_num)

#print axioms counterexample_one_third

end Graffiti363Strong
