import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-! A formalization of Claude Opus 5's counterexample to Written on the Wall II #308. -/

namespace Graffiti308

open Finset SimpleGraph

section Definitions
variable {V : Type*} (G : SimpleGraph V)

/-- Definition 94, including the requirement for vertices in the selected set. -/
def IsTotalDominating (D : Finset V) : Prop :=
  ∀ v, ∃ w ∈ D, G.Adj v w

noncomputable def totalDominationNumber : ℕ :=
  sInf {k : ℕ | ∃ D, IsTotalDominating G D ∧ D.card = k}

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Open degree in the graph induced by the remaining vertices. -/
def inducedDegree (S : Finset V) (v : V) : ℕ := (S.filter (G.Adj v)).card

theorem inducedDegree_eq (S : Finset V) (v : S) :
    inducedDegree G S v = (G.induce (S : Set V)).degree v := by
  have h : S.filter (G.Adj v) = G.neighborFinset v ∩ S := by
    ext w
    simp [and_comm]
  rw [inducedDegree, h, SimpleGraph.degree, ← card_map (Function.Embedding.subtype (S : Set V))]
  congr 1
  ext w
  simp only [mem_inter, mem_neighborFinset, mem_map]
  constructor
  · rintro ⟨ha, hw⟩
    exact ⟨⟨w, hw⟩, ha, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hx, x.property⟩

def MaxineStep (S : Finset V) (v : V) : Prop :=
  v ∈ S ∧ 0 < inducedDegree G S v ∧
    ∀ w ∈ S, inducedDegree G S w ≤ inducedDegree G S v

/-- A run may choose any maximum-degree vertex and stops exactly when no edge remains. -/
inductive MaxineTrace : Finset V → Finset V → Prop where
  | stop {S : Finset V} (h : G.IsIndepSet (S : Set V)) : MaxineTrace S S
  | delete {S T : Finset V} {v : V} (h : MaxineStep G S v) (rest : MaxineTrace (S.erase v) T) :
      MaxineTrace S T

variable {G} in
omit [Fintype V] in
theorem MaxineTrace.independent {S T : Finset V} (h : MaxineTrace G S T) :
    G.IsIndepSet (T : Set V) := by
  induction h with
  | stop h => exact h
  | delete _ _ ih => exact ih

variable {G} in
theorem MaxineTrace.card_le_indepNum {S T : Finset V} (h : MaxineTrace G S T) :
    T.card ≤ G.indepNum :=
  h.independent.card_le_indepNum

/-- Definition 111 uses the largest output, ranging over all choices at ties. -/
noncomputable def maxine : ℕ :=
  sSup {k : ℕ | ∃ T, MaxineTrace G univ T ∧ T.card = k}

def edgeNeighborhood (u v : V) : Finset V :=
  Gᶜ.neighborFinset u ∪ Gᶜ.neighborFinset v

theorem edgeNeighborhood_endpoints {u v : V} (h : Gᶜ.Adj u v) :
    u ∈ edgeNeighborhood G u v ∧ v ∈ edgeNeighborhood G u v :=
  ⟨mem_union_right _ ((Gᶜ.mem_neighborFinset v u).mpr h.symm),
    mem_union_left _ ((Gᶜ.mem_neighborFinset u v).mpr h)⟩

/-- Definitions 28 and 31. The minimum is used on a nonempty set of complement edges. -/
noncomputable def minComplementEdgeNeighborhood : ℕ :=
  sInf {k : ℕ | ∃ u v, Gᶜ.Adj u v ∧ (edgeNeighborhood G u v).card = k}

end Definitions

abbrev Branch := Fin 5
abbrev Vertex := Branch × Fin 3

def base (i : Branch) : Vertex := (i, 0)
def support (i : Branch) : Vertex := (i, 1)
def leaf (i : Branch) : Vertex := (i, 2)

/-- A copy of K₅ with edge 01 deleted, with one two-edge path appended at each vertex. -/
def witnessAdj (u v : Vertex) : Prop :=
  (u.1 = v.1 ∧ (u.2.val + 1 = v.2.val ∨ v.2.val + 1 = u.2.val)) ∨
  (u.2 = 0 ∧ v.2 = 0 ∧ u.1 ≠ v.1 ∧
    ¬ ((u.1 = 0 ∧ v.1 = 1) ∨ (u.1 = 1 ∧ v.1 = 0)))

instance (u v : Vertex) : Decidable (witnessAdj u v) := by
  unfold witnessAdj
  infer_instance

def witness : SimpleGraph Vertex where
  Adj := witnessAdj
  symm := by
    intro u v
    simp only [witnessAdj, eq_comm, ne_comm, and_comm, and_left_comm, or_comm]
    exact id
  loopless := by
    intro v
    simp [witnessAdj]

instance : DecidableRel witness.Adj := fun u v =>
  inferInstanceAs (Decidable (witnessAdj u v))

theorem order_eq : Fintype.card Vertex = 15 := by decide

private theorem base_reachable (i : Branch) : witness.Reachable (base 2) (base i) := by
  by_cases h : i = 2
  · subst i
    exact SimpleGraph.Reachable.refl _
  · apply SimpleGraph.Adj.reachable
    change witnessAdj (base 2) (base i)
    simp [witnessAdj, base, Ne.symm h]

private theorem path_edges : ∀ i : Branch, witness.Adj (base i) (support i) ∧
    witness.Adj (support i) (leaf i) := by decide

theorem witness_connected : witness.Connected := by
  apply (connected_iff_exists_forall_reachable witness).mpr
  refine ⟨base 2, ?_⟩
  rintro ⟨i,j⟩
  have h := base_reachable i
  have hr := h.trans (path_edges i).1.reachable
  have hj : j = 0 ∨ j = 1 ∨ j = 2 := by
    have : j.val < 3 := j.isLt
    omega
  rcases hj with rfl | rfl | rfl
  · exact h
  · exact hr
  · exact hr.trans (path_edges i).2.reachable

private def totalSet : Finset Vertex := univ.filter (fun v => v.2 ≠ 2)

private theorem totalSet_total : IsTotalDominating witness totalSet := by
  unfold IsTotalDominating
  decide

private def forcingVertex (i : Branch × Fin 2) : Vertex := (i.1, ⟨i.2.val + 1, by omega⟩)

set_option maxHeartbeats 5000000 in
private theorem forcing_disjoint :
    ∀ i j : Branch × Fin 2, i ≠ j → ∀ v : Vertex,
      ¬ (witness.Adj (forcingVertex i) v ∧ witness.Adj (forcingVertex j) v) := by decide

theorem totalDomination_eq : totalDominationNumber witness = 10 := by
  apply le_antisymm
  · exact Nat.sInf_le ⟨totalSet, totalSet_total, by decide⟩
  · have hn : {k : ℕ | ∃ D, IsTotalDominating witness D ∧ D.card = k}.Nonempty :=
      ⟨10, totalSet, totalSet_total, by decide⟩
    obtain ⟨D, hD, hcard⟩ := Nat.sInf_mem hn
    change 10 ≤ sInf _
    rw [← hcard]
    choose f hf ha using fun i : Branch × Fin 2 => hD (forcingVertex i)
    let e (i : Branch × Fin 2) : D := ⟨f i, hf i⟩
    have he : Function.Injective e := by
      intro i j hij
      by_contra hn
      have h : f i = f j := congrArg Subtype.val hij
      exact forcing_disjoint i j hn (f i) ⟨ha i, h ▸ ha j⟩
    simpa using Fintype.card_le_of_injective e he

private theorem outside_same_branch :
    ∀ u v : Vertex, u.2 ≠ 0 → v.2 ≠ 0 → u.1 = v.1 →
      u = v ∨ witness.Adj u v := by decide

private theorem small_base_indep :
    ∀ B : Finset Branch, (∀ i ∈ B, ∀ j ∈ B, i ≠ j → ¬ witness.Adj (base i) (base j)) →
      B.card ≤ 2 := by decide

private theorem indep_card_le_seven {S : Finset Vertex} (hS : witness.IsIndepSet (S : Set Vertex)) :
    S.card ≤ 7 := by
  change (S : Set Vertex).Pairwise (fun u v => ¬ witness.Adj u v) at hS
  let A := S.filter (fun v => v.2 = 0)
  let B := S.filter (fun v => v.2 ≠ 0)
  have hpart : A.card + B.card = S.card :=
    filter_card_add_filter_neg_card_eq_card _
  have ha : A.card ≤ 2 := by
    have hA : Set.InjOn Prod.fst (A : Set Vertex) := by
      intro u hu v hv huv
      exact Prod.ext huv ((mem_filter.mp hu).2.trans (mem_filter.mp hv).2.symm)
    rw [← card_image_of_injOn hA]
    apply small_base_indep
    intro i hi j hj hij
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hi
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hj
    have hu' : u = base u.1 := Prod.ext rfl (mem_filter.mp hu).2
    have hv' : v = base v.1 := Prod.ext rfl (mem_filter.mp hv).2
    rw [← hu', ← hv']
    exact hS (mem_filter.mp hu).1 (mem_filter.mp hv).1 (fun h => hij (congrArg Prod.fst h))
  have hb : B.card ≤ 5 := by
    have hB : Set.InjOn Prod.fst (B : Set Vertex) := by
      intro u hu v hv huv
      obtain h | h := outside_same_branch u v (mem_filter.mp hu).2 (mem_filter.mp hv).2 huv
      · exact h
      · by_contra hn
        exact hS (mem_filter.mp hu).1 (mem_filter.mp hv).1 hn h
    rw [← card_image_of_injOn hB]
    exact (card_le_univ _).trans (by decide)
  omega

def finalSet : Finset Vertex :=
  univ.filter (fun v => v.2 = 2 ∨ (v.2 = 0 ∧ (v.1 = 0 ∨ v.1 = 1)))

private theorem finalSet_indep : witness.IsIndepSet (finalSet : Set Vertex) := by decide

theorem finalSet_card : finalSet.card = 7 := by decide

theorem independence_eq : witness.indepNum = 7 := by
  apply le_antisymm
  · obtain ⟨S, hS⟩ := witness.exists_isNIndepSet_indepNum
    rw [← hS.card_eq]
    exact indep_card_le_seven hS.isIndepSet
  · rw [← finalSet_card]
    exact finalSet_indep.card_le_indepNum

set_option maxHeartbeats 5000000 in
private theorem edgeNeighborhood_lower :
    ∀ u v : Vertex, witnessᶜ.Adj u v → 12 ≤ (edgeNeighborhood witness u v).card := by decide

private theorem missing_edge : witnessᶜ.Adj (base 0) (base 1) := by decide

private theorem missing_edge_card : (edgeNeighborhood witness (base 0) (base 1)).card = 12 := by decide

theorem edgeNeighborhood_min_eq : minComplementEdgeNeighborhood witness = 12 := by
  apply le_antisymm
  · exact Nat.sInf_le ⟨base 0, base 1, missing_edge, missing_edge_card⟩
  · have hn : {k : ℕ | ∃ u v, witnessᶜ.Adj u v ∧
        (edgeNeighborhood witness u v).card = k}.Nonempty :=
      ⟨12, base 0, base 1, missing_edge, missing_edge_card⟩
    obtain ⟨u,v,h,he⟩ := Nat.sInf_mem hn
    change 12 ≤ sInf _
    rw [← he]
    exact edgeNeighborhood_lower u v h

set_option maxHeartbeats 5000000 in
theorem trace_attaining_seven : MaxineTrace witness univ finalSet := by
  refine .delete (v := base 2) (by unfold MaxineStep; decide) ?_
  refine .delete (v := base 3) (by unfold MaxineStep; decide) ?_
  refine .delete (v := base 4) (by unfold MaxineStep; decide) ?_
  refine .delete (v := support 0) (by unfold MaxineStep; decide) ?_
  refine .delete (v := support 1) (by unfold MaxineStep; decide) ?_
  refine .delete (v := support 2) (by unfold MaxineStep; decide) ?_
  refine .delete (v := support 3) (by unfold MaxineStep; decide) ?_
  refine .delete (v := support 4) (by unfold MaxineStep; decide) ?_
  have he : ((((((((univ : Finset Vertex).erase (base 2)).erase (base 3)).erase
      (base 4)).erase (support 0)).erase (support 1)).erase (support 2)).erase
      (support 3)).erase (support 4) = finalSet := by decide
  rw [he]
  exact .stop finalSet_indep

theorem maxine_eq : maxine witness = 7 := by
  apply le_antisymm
  · have hn : {k : ℕ | ∃ T, MaxineTrace witness univ T ∧ T.card = k}.Nonempty :=
      ⟨7, finalSet, trace_attaining_seven, finalSet_card⟩
    exact csSup_le hn (by
      rintro _ ⟨T,hT,rfl⟩
      exact hT.card_le_indepNum.trans_eq independence_eq)
  · apply le_csSup
    · refine ⟨15, ?_⟩
      rintro _ ⟨T,_,rfl⟩
      exact (card_le_univ T).trans_eq order_eq
    · exact ⟨finalSet, trace_attaining_seven, finalSet_card⟩

/-- The violation holds for each legal trace, regardless of how a tie is broken. -/
theorem every_trace_violates {T : Finset Vertex} (hT : MaxineTrace witness univ T) :
    T.card + minComplementEdgeNeighborhood witness < 2 * totalDominationNumber witness := by
  have hb := hT.card_le_indepNum
  rw [independence_eq] at hb
  rw [edgeNeighborhood_min_eq, totalDomination_eq]
  omega

/-- The catalogue inequality fails over the rationals for this connected graph of order 15. -/
theorem counterexample308 :
    witness.Connected ∧ 2 < Fintype.card Vertex ∧
      (∃ u v, witnessᶜ.Adj u v) ∧ (∃ D, IsTotalDominating witness D) ∧
      (1 / 2 : ℚ) * ((maxine witness : ℚ) + (minComplementEdgeNeighborhood witness : ℚ)) <
        (totalDominationNumber witness : ℚ) := by
  refine ⟨witness_connected, by decide, ⟨base 0, base 1, missing_edge⟩,
    ⟨totalSet, totalSet_total⟩, ?_⟩
  rw [maxine_eq, edgeNeighborhood_min_eq, totalDomination_eq]
  norm_num

#print axioms inducedDegree_eq
#print axioms MaxineTrace.card_le_indepNum
#print axioms every_trace_violates
#print axioms counterexample308

end Graffiti308
