import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

open SimpleGraph Finset
set_option maxRecDepth 4096
set_option maxHeartbeats 12000000
namespace Graffiti351
abbrev V := Fin 48
def E : List (V × V) := [(0, 1), (0, 12), (0, 30), (1, 2), (1, 3), (3, 4), (4, 5), (5, 6), (5, 7), (7, 8), (7, 10), (8, 9), (10, 11), (12, 13), (12, 14), (14, 15), (15, 16), (15, 23), (16, 17), (16, 18), (18, 19), (18, 21), (19, 20), (21, 22), (23, 24), (23, 25), (25, 26), (25, 28), (26, 27), (28, 29), (30, 31), (30, 32), (32, 33), (33, 34), (33, 41), (34, 35), (34, 36), (36, 37), (36, 39), (37, 38), (39, 40), (41, 42), (41, 43), (43, 44), (43, 46), (44, 45), (46, 47)]
def parentOf (v : V) : V := ([0, 0, 1, 1, 3, 4, 5, 5, 7, 8, 7, 10, 0, 12, 12, 14, 15, 16, 16, 18, 19, 18, 21, 15, 23, 23, 25, 26, 25, 28, 0, 30, 30, 32, 33, 34, 34, 36, 37, 36, 39, 33, 41, 41, 43, 44, 43, 46] : List V).getD v.val 0
def G : SimpleGraph V where
  Adj x y := x ≠ y ∧ ((x ≠ 0 ∧ parentOf x = y) ∨ (y ≠ 0 ∧ parentOf y = x))
  symm := fun _ _ h => ⟨h.1.symm,h.2.symm⟩
  loopless := fun _ h => h.1 rfl
instance : DecidableRel G.Adj := fun x y => inferInstanceAs
  (Decidable (x ≠ y ∧ ((x ≠ 0 ∧ parentOf x = y) ∨ (y ≠ 0 ∧ parentOf y = x))))
def degreeFast (v : V) : Nat := ([3, 3, 1, 2, 2, 3, 1, 3, 2, 1, 2, 1, 3, 1, 2, 3, 3, 1, 3, 2, 1, 2, 1, 3, 1, 3, 2, 1, 2, 1, 3, 1, 2, 3, 3, 1, 3, 2, 1, 2, 1, 3, 1, 3, 2, 1, 2, 1] : List Nat).getD v.val 0
set_option maxHeartbeats 4000000 in
lemma degree_eq : ∀ v, G.degree v = degreeFast v := by
  intro v
  fin_cases v <;> decide +kernel
def supportOrLeaf (v : V) : Prop := degreeFast v = 1 ∨ ∃ w, G.Adj v w ∧ degreeFast w = 1
def closedDegreeTwo (v : V) : Prop := degreeFast v = 2 ∨ ∃ w, G.Adj v w ∧ degreeFast w = 2
instance (v : V) : Decidable (supportOrLeaf v) := by unfold supportOrLeaf; infer_instance
instance (v : V) : Decidable (closedDegreeTwo v) := by unfold closedDegreeTwo; infer_instance
def labelA (v : V) : Fin 18 := ([0, 0, 0, 0, 0, 1, 1, 0, 2, 2, 3, 3, 4, 4, 0, 0, 5, 5, 0, 6, 6, 7, 7, 8, 8, 0, 9, 9, 10, 10, 11, 11, 0, 0, 12, 12, 0, 13, 13, 14, 14, 15, 15, 0, 16, 16, 17, 17] : List (Fin 18)).getD v.val 0
def labelB (v : V) : Fin 7 := ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 2, 2, 2, 2, 2, 0, 0, 3, 3, 3, 3, 3, 4, 0, 4, 4, 0, 0, 5, 5, 5, 5, 5, 0, 0, 6, 6, 6, 6, 6] : List (Fin 7)).getD v.val 0
def selected : Finset V := {0, 1, 5, 7, 8, 10, 12, 16, 18, 19, 21, 23, 25, 26, 28, 30, 34, 36, 37, 39, 41, 43, 44, 46}
lemma rootReach (v : V) : G.Reachable 0 v := by
  have step : ∀ x : V, x = 0 ∨ (parentOf x).val < x.val ∧ G.Adj (parentOf x) x := by decide +kernel
  generalize h : v.val = n
  induction n using Nat.strong_induction_on generalizing v with
  | h n ih =>
    rcases step v with rfl | ⟨hu,e⟩
    · exact ⟨Walk.nil⟩
    · exact (ih (parentOf v).val (h ▸ hu) (parentOf v) rfl).trans e.reachable

lemma gTree : G.IsTree := by
  apply isTree_iff_connected_and_card.mpr
  refine ⟨(connected_iff_exists_forall_reachable _).mpr ⟨0,rootReach⟩,?_⟩
  have h := G.sum_degrees_eq_twice_card_edges
  have hd : (∑ v : V, G.degree v) = 94 := by simp only [degree_eq]; decide
  rw [hd] at h
  simp only [Nat.card_eq_fintype_card, ← edgeFinset_card, Fintype.card_fin]
  omega

lemma componentLower {W : Type} [Finite W] (H : SimpleGraph W)
    {k : ℕ} (lab : W → Fin k) (hl : ∀ a b, H.Adj a b → lab a = lab b)
    (hs : Function.Surjective lab) : k ≤ Nat.card H.ConnectedComponent := by
  let f : H.ConnectedComponent → Fin k := Quot.lift lab (by
    intro a b hr
    obtain ⟨w⟩ := hr
    induction w with
    | nil => rfl
    | @cons x y z e p ih => exact (hl x y e).trans ih)
  letI : Finite H.ConnectedComponent := Finite.of_surjective H.connectedComponentMk (fun c => Quot.exists_rep c)
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨y,hy⟩ := hs x
    exact ⟨H.connectedComponentMk y,hy⟩
  simpa using Nat.card_le_card_of_surjective f hsurj

lemma lowerA : 18 ≤ Nat.card (G.induce {v | supportOrLeaf v}).ConnectedComponent := by
  apply componentLower _ (fun v => labelA v.val)
  · have h : ∀ x : V, supportOrLeaf x → supportOrLeaf (parentOf x) →
        labelA x = labelA (parentOf x) := by decide +kernel
    intro a b e
    rcases e.2 with ⟨_, e⟩ | ⟨_,e⟩
    · change parentOf a.val = b.val at e
      have he := h a.val a.property (e.symm ▸ b.property)
      rwa [e] at he
    · change parentOf b.val = a.val at e
      have he := h b.val b.property (e.symm ▸ a.property)
      rw [e] at he
      exact he.symm
  · have h : ∀ i : Fin 18, ∃ x, labelA x = i ∧ supportOrLeaf x := by decide +kernel
    intro i
    obtain ⟨x,he,hx⟩ := h i
    exact ⟨⟨x,hx⟩,he⟩

lemma lowerB : 7 ≤ Nat.card (G.induce {v | closedDegreeTwo v}).ConnectedComponent := by
  apply componentLower _ (fun v => labelB v.val)
  · have h : ∀ x : V, closedDegreeTwo x → closedDegreeTwo (parentOf x) →
        labelB x = labelB (parentOf x) := by decide +kernel
    intro a b e
    rcases e.2 with ⟨_, e⟩ | ⟨_,e⟩
    · change parentOf a.val = b.val at e
      have he := h a.val a.property (e.symm ▸ b.property)
      rwa [e] at he
    · change parentOf b.val = a.val at e
      have he := h b.val b.property (e.symm ▸ a.property)
      rw [e] at he
      exact he.symm
  · have h : ∀ i : Fin 7, ∃ x, labelB x = i ∧ closedDegreeTwo x := by decide +kernel
    intro i
    obtain ⟨x,he,hx⟩ := h i
    exact ⟨⟨x,hx⟩,he⟩

def IsTotalDominating {U : Type} (T : SimpleGraph U) (D : Finset U) : Prop :=
  ∀ v, ∃ w, w ∈ D ∧ T.Adj v w

noncomputable def totalDominationNumber {U : Type} (T : SimpleGraph U) : ℕ :=
  sInf {k | ∃ D, IsTotalDominating T D ∧ D.card = k}

def Conjecture351 : Prop :=
  ∀ (U : Type) [Fintype U] [DecidableEq U] (T : SimpleGraph U) [DecidableRel T.Adj],
    T.IsTree → 2 < Fintype.card U →
    Nat.card (T.induce {v | T.degree v = 1 ∨ ∃ w, T.Adj v w ∧ T.degree w = 1}).ConnectedComponent +
    Nat.card (T.induce {v | T.degree v = 2 ∨ ∃ w, T.Adj v w ∧ T.degree w = 2}).ConnectedComponent
       ≤ totalDominationNumber T

theorem not_conjecture351 : ¬ Conjecture351 := by
  intro h
  have hh := h V G gTree (by decide +kernel)
  have ht : IsTotalDominating G selected := by unfold IsTotalDominating; decide
  have hc : selected.card = 24 := by decide +kernel
  have hb : totalDominationNumber G ≤ 24 := Nat.sInf_le ⟨selected,ht,hc⟩
  have ha := lowerA
  have hb' := lowerB
  have hA : {v : V | G.degree v = 1 ∨ ∃ w, G.Adj v w ∧ G.degree w = 1} =
      {v | supportOrLeaf v} := by
    ext v
    change (G.degree v = 1 ∨ ∃ w, G.Adj v w ∧ G.degree w = 1) ↔ supportOrLeaf v
    simp only [supportOrLeaf, degree_eq]
  have hB : {v : V | G.degree v = 2 ∨ ∃ w, G.Adj v w ∧ G.degree w = 2} =
      {v | closedDegreeTwo v} := by
    ext v
    change (G.degree v = 2 ∨ ∃ w, G.Adj v w ∧ G.degree w = 2) ↔ closedDegreeTwo v
    simp only [closedDegreeTwo, degree_eq]
  rw [hA,hB] at hh
  omega

#print axioms not_conjecture351
end Graffiti351
