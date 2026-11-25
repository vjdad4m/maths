import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.List.Sort
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

open SimpleGraph Finset
set_option maxRecDepth 4096
set_option maxHeartbeats 12000000
namespace Graffiti369

def normalize (l : List ℕ) : List ℕ := List.insertionSort (fun a b => b ≤ a) l
def hhStep : List ℕ → List ℕ
  | [] => []
  | d::xs => normalize ((xs.take d).map (fun x => x-1) ++ xs.drop d)
theorem hhStep_length (l : List ℕ) : (hhStep l).length = l.length - 1 := by
  cases l with
  | nil => rfl
  | cons d l => simp [hhStep,normalize,List.length_take]; omega

def firstZero (l : List ℕ) : ℕ :=
  match l with
  | [] => 0
  | d::xs => if 0 ∈ d::xs then 0 else 1+firstZero (hhStep (d::xs))
termination_by l.length
decreasing_by
  rw [hhStep_length]
  simp

def degreeFreq {U : Type} [Fintype U] (T : SimpleGraph U) [DecidableRel T.Adj] (d : ℕ) : ℕ :=
  (univ.filter (fun v => T.degree v = d)).card

def modalCount {U : Type} [Fintype U] (T : SimpleGraph U) [DecidableRel T.Adj] : ℕ :=
  ((Finset.range (Fintype.card U)).filter
    (fun i => ∀ j : Fin (Fintype.card U), degreeFreq T j.val ≤ degreeFreq T i)).card

def TotallyDominates {U : Type} (T : SimpleGraph U) (D : Finset U) : Prop :=
  ∀ v, ∃ w, w ∈ D ∧ T.Adj v w

noncomputable def totalDomination {U : Type} (T : SimpleGraph U) : ℕ :=
  sInf {k | ∃ D, TotallyDominates T D ∧ D.card = k}

def Conjecture369 : Prop :=
  ∀ (n : ℕ) (T : SimpleGraph (Fin n)) [DecidableRel T.Adj],
    T.IsTree → 2 < n →
    modalCount T + (n % 2) * firstZero (normalize (List.ofFn (fun v => T.degree v)))
      ≤ totalDomination T

abbrev V := Fin 29
def parentOf (v : V) : V := ([0, 0, 1, 2, 3, 1, 0, 6, 7, 1, 1, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 7, 7, 7, 8, 8, 8, 8] : List V).getD v.val 0
def G : SimpleGraph V where
  Adj x y := x ≠ y ∧ ((x ≠ 0 ∧ parentOf x = y) ∨ (y ≠ 0 ∧ parentOf y = x))
  symm := fun _ _ h => ⟨h.1.symm,h.2.symm⟩
  loopless := fun _ h => h.1 rfl
instance : DecidableRel G.Adj := fun x y => inferInstanceAs
  (Decidable (x ≠ y ∧ ((x ≠ 0 ∧ parentOf x = y) ∨ (y ≠ 0 ∧ parentOf y = x))))

def degreeFast (v : V) : ℕ := ([2, 5, 2, 5, 5, 5, 2, 5, 5, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List ℕ).getD v.val 0
lemma degree_eq : ∀ v, G.degree v = degreeFast v := by
  intro v
  fin_cases v <;> decide +kernel

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
  have hd : (∑ v : V, G.degree v) = 56 := by simp only [degree_eq]; decide +kernel
  rw [hd] at h
  simp only [Nat.card_eq_fintype_card, ← edgeFinset_card, Fintype.card_fin]
  omega

def selected : Finset V := {1,3,4,5,7,8}

lemma gamma_le : totalDomination G ≤ 6 := by
  have h : TotallyDominates G selected := by unfold TotallyDominates; decide +kernel
  have hc : selected.card = 6 := by decide
  exact Nat.sInf_le ⟨selected,h,hc⟩

lemma mode_eq : modalCount G = 1 := by
  unfold modalCount degreeFreq
  simp_rw [degree_eq]
  decide +kernel

private def l0 : List ℕ := [5, 5, 5, 5, 5, 5, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
private def l1 : List ℕ := [4, 4, 4, 4, 4, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
private def l2 : List ℕ := [3, 3, 3, 3, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
private def l3 : List ℕ := [2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
private def l4 : List ℕ := [2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
private def l5 : List ℕ := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
private def l6 : List ℕ := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0]

lemma firstZero_next {l : List ℕ} (hn : l ≠ []) (h : 0 ∉ l) :
    firstZero l = 1 + firstZero (hhStep l) := by
  cases l with
  | nil => exact False.elim (hn rfl)
  | cons d xs => rw [firstZero, if_neg h]

lemma firstZero_stop {l : List ℕ} (h : 0 ∈ l) : firstZero l = 0 := by
  cases l with
  | nil => simp at h
  | cons d xs => rw [firstZero, if_pos h]

lemma step_eq : firstZero (normalize (List.ofFn (fun v : V => G.degree v))) = 6 := by
  rw [show (fun v : V => G.degree v) = degreeFast from funext degree_eq]
  have h0 : normalize (List.ofFn degreeFast) = l0 := by decide +kernel
  rw [h0]
  calc
    firstZero l0 = 1 + firstZero l1 := by
      have he : hhStep l0 = l1 := by decide +kernel
      rw [firstZero_next (l := l0) (by decide) (by decide), he]
    1 + firstZero l1 = 2 + firstZero l2 := by
      have he : hhStep l1 = l2 := by decide +kernel
      rw [firstZero_next (l := l1) (by decide) (by decide), he]
      omega
    2 + firstZero l2 = 3 + firstZero l3 := by
      have he : hhStep l2 = l3 := by decide +kernel
      rw [firstZero_next (l := l2) (by decide) (by decide), he]
      omega
    3 + firstZero l3 = 4 + firstZero l4 := by
      have he : hhStep l3 = l4 := by decide +kernel
      rw [firstZero_next (l := l3) (by decide) (by decide), he]
      omega
    4 + firstZero l4 = 5 + firstZero l5 := by
      have he : hhStep l4 = l5 := by decide +kernel
      rw [firstZero_next (l := l4) (by decide) (by decide), he]
      omega
    5 + firstZero l5 = 6 + firstZero l6 := by
      have he : hhStep l5 = l6 := by decide +kernel
      rw [firstZero_next (l := l5) (by decide) (by decide), he]
      omega
    _ = 6 := by rw [firstZero_stop (l := l6) (by decide)]

theorem not_conjecture369 : ¬ Conjecture369 := by
  intro h
  have hb := h 29 G gTree (by decide)
  rw [mode_eq,step_eq] at hb
  have hu := gamma_le
  omega

#print axioms not_conjecture369
end Graffiti369
