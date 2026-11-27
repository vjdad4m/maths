import Theta

namespace Theta659
open Finset SimpleGraph
open scoped BigOperators
variable {V' : Type*} {k : ℕ}

/-- The Roman labeling and optimum definitions used in the row 621 proof. -/
def Roman (G : SimpleGraph V') (f : V' → Fin 3) : Prop :=
  ∀ v, f v = 0 → ∃ u, G.Adj v u ∧ f u = 2

noncomputable def romanNumber [Fintype V'] (G : SimpleGraph V') :=
  sInf {n | ∃ f : V' → Fin 3, Roman G f ∧ ∑ v, (f v : ℕ) = n}

private def hubLabel : V k → Fin 3
  | (_,none) => 2
  | (_,some _) => 0

theorem roman_upper : romanNumber (graph k) ≤ 4 := by
  apply Nat.sInf_le
  refine ⟨hubLabel,?_,?_⟩
  · rintro ⟨b,_|i⟩ zero
    · exact ((by decide : (2 : Fin 3) ≠ 0) zero).elim
    · exact ⟨hub b,rfl,rfl⟩
  · simp [V,Fintype.sum_prod_type,Fintype.sum_option,hubLabel]

private def halfWeight (f : V k → Fin 3) (b : Bool) : ℕ :=
  (f (hub b)).val + ∑ i : Fin k, (f (inner i b)).val

private theorem half_sum (f : V k → Fin 3) :
    (∑ v, (f v).val) = halfWeight f true + halfWeight f false := by
  simp [V,halfWeight,Fintype.sum_prod_type,Fintype.sum_option]

/-- If a hub and the internals on its side carry at most one unit, the hub
has that unit and every opposite internal vertex must have label two. -/
theorem light_side {f : V k → Fin 3} (hf : Roman (graph k) f) {b : Bool}
    (light : halfWeight f b ≤ 1) : ∀ i : Fin k, f (inner i (!b)) = 2 := by
  have item (i : Fin k) : (f (inner i b)).val ≤ ∑ j : Fin k, (f (inner j b)).val :=
    single_le_sum (f := fun j : Fin k => (f (inner j b)).val) (fun _ _ => Nat.zero_le _) (mem_univ i)
  have positive : f (hub b) ≠ 0 := by
    intro hz
    obtain ⟨⟨c,_|j⟩,adj,two⟩ := hf (hub b) hz
    · exact adj
    · change b=c at adj
      subst c
      have h := item j
      change f (inner j b) = 2 at two
      simp [halfWeight] at light
      rw [two] at h
      omega
  intro i
  have zero : f (inner i b) = 0 := by
    have h := item i
    have pos : 0 < (f (hub b)).val := by
      by_contra! z
      exact positive (Fin.ext (by simpa using z))
    unfold halfWeight at light
    apply Fin.ext
    change (f (inner i b)).val = 0
    omega
  obtain ⟨⟨c,_|j⟩,adj,two⟩ := hf (inner i b) zero
  · change b=c at adj
    subst c
    change f (hub b) = 2 at two
    unfold halfWeight at light
    rw [two] at light
    omega
  · change i=j ∧ b≠c at adj
    obtain ⟨rfl,ne⟩ := adj
    have eq : c = !b := by cases b <;> cases c <;> simp_all
    subst c
    exact two

theorem roman_exact (hk : 2 ≤ k) : romanNumber (graph k) = 4 := by
  let sizes := {n | ∃ f : V k → Fin 3, Roman (graph k) f ∧ ∑ v, (f v).val = n}
  have feasible : sizes.Nonempty := ⟨_,fun _ => 1,fun _ h => ((by decide : (1 : Fin 3) ≠ 0) h).elim,rfl⟩
  obtain ⟨f,hf,weight⟩ := Nat.sInf_mem feasible
  change (∑ v, (f v).val) = romanNumber (graph k) at weight
  rw [half_sum] at weight
  have cheap (b : Bool) (h : halfWeight f b ≤ 1) : 4 ≤ halfWeight f (!b) := by
    have all := light_side hf h
    unfold halfWeight
    simp [all]
    omega
  have a := cheap true
  have b := cheap false
  simp only [Bool.not_true,Bool.not_false] at a b
  have ub := @roman_upper k
  omega

#print axioms roman_exact
end Theta659
