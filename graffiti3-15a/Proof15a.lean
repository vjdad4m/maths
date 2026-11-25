/-
Counterexample to Davila Graffiti³ #15(a): the conjugacy-class lower threshold does not force solvability. Lean uses S₅ × D₈ × D₈ (dihedral factors of order eight), verifies order 7680, center ≤ 4, class count ≥ 150, and nonsolvability. The equivalent conjectures #16 and #19 are not counted again.
Source: Randy Davila, Graffiti³ (Research Square v1), https://doi.org/10.21203/rs.3.rs-8493329/v1
Reproduce in a project pinned to Lean 4.19.0 and Mathlib v4.19.0 with lake env lean.
AI-assisted work shared for review; this is not a claim of priority.
-/

import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.Solvable
import Mathlib.Algebra.Group.ConjFinite
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.Perm
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

namespace GraffitiThree15a
set_option maxHeartbeats 15000000
set_option maxRecDepth 20000
open DihedralGroup

private abbrev S := Equiv.Perm (Fin 5)
private abbrev D := DihedralGroup 4
private abbrev G := S × D × D

private def c3 : S := ⟨![1,2,0,3,4],![2,0,1,3,4],by decide,by decide⟩
private def c4 : S := ⟨![1,2,3,0,4],![3,0,1,2,4],by decide,by decide⟩
private def c5 : S := ⟨![1,2,3,4,0],![4,0,1,2,3],by decide,by decide⟩
private def c6 : S := ⟨![1,2,0,4,3],![2,0,1,4,3],by decide,by decide⟩

private def permRep (i : Fin 6) : S :=
  match i.val with
  | 0 => 1
  | 1 => Equiv.swap 0 1
  | 2 => c3
  | 3 => c4
  | 4 => c5
  | _ => c6

private def powSignature (x : S) : List Bool :=
  (List.range 7).map (fun j => decide (x^j=1))

private theorem conjugate_preserves_signature {x y : S} (h : IsConj x y) :
    powSignature x = powSignature y := by
  apply List.map_congr_left
  intro n _
  have hh := h.pow n
  have ht : x^n = 1 ↔ y^n = 1 :=
    ⟨fun e => isConj_one_right.mp (e ▸ hh), fun e => isConj_one_left.mp (e ▸ hh)⟩
  by_cases hx : x^n = 1
  · simp [hx,ht.mp hx]
  · have hy : ¬y^n=1 := fun e => hx (ht.mpr e)
    simp [hx,hy]

private theorem permRep_inj_conj (i j : Fin 6) (h : IsConj (permRep i) (permRep j)) : i=j := by
  exact (by decide : ∀ i j : Fin 6, powSignature (permRep i) = powSignature (permRep j) → i=j)
    i j (conjugate_preserves_signature h)

private def dRep (i : Fin 5) : D :=
  match i.val with
  | 0 => r 0
  | 1 => r 1
  | 2 => r 2
  | 3 => sr 0
  | _ => sr 1

private theorem dRep_inj_conj (i j : Fin 5) (h : IsConj (dRep i) (dRep j)) : i=j := by
  obtain ⟨g,e⟩ := isConj_iff.mp h
  cases g with
  | r x =>
    exact (by decide : ∀ (i j : Fin 5) (x : ZMod 4), r x * dRep i * (r x)⁻¹ = dRep j → i=j)
      i j x e
  | sr x =>
    exact (by decide : ∀ (i j : Fin 5) (x : ZMod 4), sr x * dRep i * (sr x)⁻¹ = dRep j → i=j)
      i j x e

private theorem class_count : 150 ≤ Nat.card (ConjClasses G) := by
  let f : Fin 6 × Fin 5 × Fin 5 → ConjClasses G :=
    fun i => ConjClasses.mk (permRep i.1, dRep i.2.1, dRep i.2.2)
  have hf : Function.Injective f := by
    intro i j h
    have hc := ConjClasses.mk_eq_mk_iff_isConj.mp h
    obtain ⟨g,e⟩ := isConj_iff.mp hc
    have h0 := permRep_inj_conj i.1 j.1 (isConj_iff.mpr ⟨g.1,congrArg Prod.fst e⟩)
    have h1 := dRep_inj_conj i.2.1 j.2.1 (isConj_iff.mpr ⟨g.2.1,congrArg (fun p => p.2.1) e⟩)
    have h2 := dRep_inj_conj i.2.2 j.2.2 (isConj_iff.mpr ⟨g.2.2,congrArg (fun p => p.2.2) e⟩)
    exact Prod.ext h0 (Prod.ext h1 h2)
  simpa [Nat.card_prod] using Nat.card_le_card_of_injective f hf

private theorem center_s (p : S) (h : p ∈ Subgroup.center S) : p=1 := by
  have hc := Subgroup.mem_center_iff.mp h
  have hcy (i : Fin 5) : p (c5 i) = c5 (p i) :=
    (congrArg (fun q : S => q i) (hc c5)).symm
  have hsw (i : Fin 5) : p ((Equiv.swap 0 1) i) = (Equiv.swap 0 1) (p i) :=
    (congrArg (fun q : S => q i) (hc (Equiv.swap 0 1))).symm
  have he : (Equiv.swap 0 1) (p 0) = c5 (p 0) := (hsw 0).symm.trans (hcy 0)
  have hp0 : p 0 = 0 :=
    (by decide : ∀ i : Fin 5, (Equiv.swap 0 1) i = c5 i → i=0) (p 0) he
  have hp1 : p 1 = 1 := by
    have h := hcy 0
    change p 1 = c5 (p 0) at h
    rw [hp0] at h
    exact h
  have hp2 : p 2 = 2 := by
    have h := hcy 1
    change p 2 = c5 (p 1) at h
    rw [hp1] at h
    exact h
  have hp3 : p 3 = 3 := by
    have h := hcy 2
    change p 3 = c5 (p 2) at h
    rw [hp2] at h
    exact h
  have hp4 : p 4 = 4 := by
    have h := hcy 3
    change p 4 = c5 (p 3) at h
    rw [hp3] at h
    exact h
  apply Equiv.ext
  intro i
  change p i = i
  fin_cases i <;> first | exact hp0 | exact hp1 | exact hp2 | exact hp3 | exact hp4

private theorem center_d (d : D) (h : d ∈ Subgroup.center D) : d=r 0 ∨ d=r 2 := by
  have hc := Subgroup.mem_center_iff.mp h
  have hr := hc (r 1)
  have hs := hc (sr 0)
  cases d with
  | r i =>
    exact (by decide : ∀ i : ZMod 4, r 1 * r i = r i * r 1 →
      sr 0 * r i = r i * sr 0 → r i=r 0 ∨ r i=r 2) i hr hs
  | sr i =>
    exact (by decide : ∀ i : ZMod 4, r 1 * sr i = sr i * r 1 →
      sr 0 * sr i = sr i * sr 0 → sr i=r 0 ∨ sr i=r 2) i hr hs

private theorem center_bound : Nat.card (Subgroup.center G) ≤ 4 := by
  let f : Subgroup.center G → Bool × Bool := fun g =>
    (decide (g.1.2.1 = r 2), decide (g.1.2.2 = r 2))
  have test (g : Subgroup.center G) :
      g.1.1=1 ∧ (g.1.2.1=r 0 ∨ g.1.2.1=r 2) ∧ (g.1.2.2=r 0 ∨ g.1.2.2=r 2) := by
    have hc := Subgroup.mem_center_iff.mp g.2
    refine ⟨center_s _ ?_, center_d _ ?_, center_d _ ?_⟩
    · exact Subgroup.mem_center_iff.mpr (fun x => congrArg Prod.fst (hc (x,1,1)))
    · exact Subgroup.mem_center_iff.mpr (fun x => congrArg (fun y => y.2.1) (hc (1,x,1)))
    · exact Subgroup.mem_center_iff.mpr (fun x => congrArg (fun y => y.2.2) (hc (1,1,x)))
  have hbit (a b : D) (ha : a=r 0 ∨ a=r 2) (hb : b=r 0 ∨ b=r 2)
      (h : decide (a=r 2) = decide (b=r 2)) : a=b := by
    have h02 : (1 : D) ≠ r 2 := by decide
    rcases ha with rfl|rfl <;> rcases hb with rfl|rfl <;> simp [h02] at h ⊢
  have hf : Function.Injective f := by
    intro a b hh
    have ha := test a
    have hb := test b
    have h1 := hbit _ _ ha.2.1 hb.2.1 (congrArg Prod.fst hh)
    have h2 := hbit _ _ ha.2.2 hb.2.2 (congrArg Prod.snd hh)
    exact Subtype.ext (Prod.ext (ha.1.trans hb.1.symm) (Prod.ext h1 h2))
  simpa [Nat.card_prod, Nat.card_eq_fintype_card] using Nat.card_le_card_of_injective f hf

private theorem order : Nat.card G = 7680 := by
  simp only [Nat.card_prod, DihedralGroup.nat_card]
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  decide

private theorem nonsolvable : ¬ IsSolvable G := by
  intro h
  letI : IsSolvable G := h
  have hs : IsSolvable S := solvable_of_surjective (f := MonoidHom.fst S (D×D))
    (fun x => ⟨(x,1,1),rfl⟩)
  exact Equiv.Perm.fin_5_not_solvable hs

/-- Exact Graffiti³ #15(a), using real square root and the actual finite-group invariants. -/
def Conjecture15a : Prop :=
  ∀ (T : Type) [Group T] [Finite T],
    (Nat.card (Subgroup.center T) : ℝ) / 4 +
       3/4 * Real.sqrt ((Nat.card (Subgroup.center T) : ℝ) * Nat.card T)
      ≤ (Nat.card (ConjClasses T) : ℝ) → IsSolvable T

theorem graffiti3_conj15a_false : ¬ Conjecture15a := by
  intro h
  apply nonsolvable
  apply h G
  rw [order]
  have hz : (Nat.card (Subgroup.center G) : ℝ) ≤ 4 := by exact_mod_cast center_bound
  have hk : (150 : ℝ) ≤ Nat.card (ConjClasses G) := by exact_mod_cast class_count
  have hle : Real.sqrt ((Nat.card (Subgroup.center G) : ℝ) * (7680 : ℝ)) ≤ 176 := by
    apply (Real.sqrt_le_iff).2
    constructor
    · norm_num
    · calc
        _ ≤ (4:ℝ)*7680 := mul_le_mul_of_nonneg_right hz (by norm_num)
        _ ≤ _ := by norm_num
  calc
    _ ≤ (4:ℝ)/4 + 3/4*176 := add_le_add
      (div_le_div_of_nonneg_right hz (by norm_num))
      (mul_le_mul_of_nonneg_left hle (by norm_num))
    _ ≤ 150 := by norm_num
    _ ≤ _ := hk

#print axioms graffiti3_conj15a_false
end GraffitiThree15a
