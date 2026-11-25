/-
Counterexample to Davila Graffiti³ #21 on finite nilpotent groups. The order-512 wreath product D₁₆ ≀ C₂ gives at most 35 conjugacy classes against a required lower bound of at least 57.
Source: Randy Davila, Graffiti³ (Research Square v1), https://doi.org/10.21203/rs.3.rs-8493329/v1
Reproduce in a project pinned to Lean 4.19.0 and Mathlib v4.19.0 with lake env lean.
AI-assisted work shared for review; this is not a claim of priority.
-/

import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Abelianization
import Mathlib.Algebra.Group.ConjFinite
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.NormNum

namespace GraffitiThree2122
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
open DihedralGroup

/-- Wreath product by the transposition action of C₂ on H × H. -/
structure Wreath (H : Type) where
  a : H
  b : H
  flip : Bool
  deriving DecidableEq

private def wMul {H : Type} [Group H] (x y : Wreath H) : Wreath H :=
  if x.flip then ⟨x.a * y.b, x.b * y.a, !y.flip⟩ else ⟨x.a * y.a, x.b * y.b, y.flip⟩

private def wInv {H : Type} [Group H] (x : Wreath H) : Wreath H :=
  if x.flip then ⟨x.b⁻¹, x.a⁻¹, true⟩ else ⟨x.a⁻¹,x.b⁻¹,false⟩

instance {H : Type} [Group H] : Group (Wreath H) where
  mul := wMul
  one := ⟨1,1,false⟩
  inv := wInv
  mul_assoc := by
    rintro ⟨a,b,f⟩ ⟨c,d,g⟩ ⟨e,h,j⟩
    change wMul (wMul ⟨a,b,f⟩ ⟨c,d,g⟩) ⟨e,h,j⟩ =
      wMul ⟨a,b,f⟩ (wMul ⟨c,d,g⟩ ⟨e,h,j⟩)
    cases f <;> cases g <;> cases j <;> simp [wMul, mul_assoc]
  one_mul := by
    rintro ⟨a,b,f⟩
    change wMul ⟨1,1,false⟩ ⟨a,b,f⟩ = ⟨a,b,f⟩
    simp [wMul]
  mul_one := by
    rintro ⟨a,b,f⟩
    change wMul ⟨a,b,f⟩ ⟨1,1,false⟩ = ⟨a,b,f⟩
    cases f <;> simp [wMul]
  inv_mul_cancel := by
    rintro ⟨a,b,f⟩
    change wMul (wInv ⟨a,b,f⟩) ⟨a,b,f⟩ = ⟨1,1,false⟩
    cases f <;> simp [wMul,wInv]

@[simp] private theorem wf_mul {H : Type} [Group H] (a b : H) (y : Wreath H) :
    (Wreath.mk a b false) * y = ⟨a*y.a,b*y.b,y.flip⟩ := rfl
@[simp] private theorem wt_mul {H : Type} [Group H] (a b : H) (y : Wreath H) :
    (Wreath.mk a b true) * y = ⟨a*y.b,b*y.a,!y.flip⟩ := rfl
@[simp] private theorem wf_inv {H : Type} [Group H] (a b : H) :
    (Wreath.mk a b false)⁻¹ = ⟨a⁻¹,b⁻¹,false⟩ := rfl
@[simp] private theorem wt_inv {H : Type} [Group H] (a b : H) :
    (Wreath.mk a b true)⁻¹ = ⟨b⁻¹,a⁻¹,true⟩ := rfl

private def equivProd (H : Type) : Wreath H ≃ H × H × Bool where
  toFun w := (w.a,w.b,w.flip)
  invFun w := ⟨w.1,w.2.1,w.2.2⟩
  left_inv := by rintro ⟨a,b,f⟩; rfl
  right_inv := by rintro ⟨a,b,f⟩; rfl
instance {H : Type} [Fintype H] : Fintype (Wreath H) :=
  Fintype.ofEquiv _ (equivProd H).symm

private abbrev H := DihedralGroup 8
private abbrev W := Wreath H

private theorem w_card : Nat.card W = 512 := by
  rw [Nat.card_congr (equivProd H), Nat.card_prod, Nat.card_prod, DihedralGroup.nat_card]
  norm_num

private def hRep (i : Fin 7) : H :=
  if i.val < 5 then r (i.val : ZMod 8) else sr ((i.val-5 : ℕ) : ZMod 8)

private def hLabel : H → Fin 7
  | r i => ⟨min i.val (8-i.val), by have := ZMod.val_lt i; omega⟩
  | sr i => ⟨5+i.val%2, by omega⟩

private def hConjugator : H → H
  | r i => if 4 < i.val then sr 0 else 1
  | sr i => r ((i.val/2 : ℕ) : ZMod 8)

private theorem h_can (h : H) : IsConj h (hRep (hLabel h)) := by
  apply isConj_iff.mpr
  refine ⟨hConjugator h, ?_⟩
  cases h with
  | r i =>
    exact (by decide : ∀ j : ZMod 8, hConjugator (r j) * r j * (hConjugator (r j))⁻¹ =
      hRep (hLabel (r j))) i
  | sr i =>
    exact (by decide : ∀ j : ZMod 8, hConjugator (sr j) * sr j * (hConjugator (sr j))⁻¹ =
      hRep (hLabel (sr j))) i

private abbrev PairIndex := {p : Fin 7 × Fin 7 // p.1 ≤ p.2}
private abbrev RepIndex := PairIndex ⊕ Fin 7

private def wRep : RepIndex → W
  | .inl x => ⟨hRep x.1.1,hRep x.1.2,false⟩
  | .inr x => ⟨hRep x,1,true⟩

private theorem conj_base {a b c d : H} (ha : IsConj a c) (hb : IsConj b d) :
    IsConj (Wreath.mk a b false) (Wreath.mk c d false) := by
  obtain ⟨x,hx⟩ := isConj_iff.mp ha
  obtain ⟨y,hy⟩ := isConj_iff.mp hb
  exact isConj_iff.mpr ⟨⟨x,y,false⟩, by simp [hx,hy]⟩

private theorem conj_swap (a b : H) :
    IsConj (Wreath.mk a b false) (Wreath.mk b a false) :=
  isConj_iff.mpr ⟨⟨1,1,true⟩,by simp⟩

private theorem conj_flip_shape (a b : H) :
    IsConj (Wreath.mk a b true) (Wreath.mk (a*b) 1 true) :=
  isConj_iff.mpr ⟨⟨1,b⁻¹,false⟩,by simp⟩

private theorem conj_flip_reduce {a c : H} (h : IsConj a c) :
    IsConj (Wreath.mk a 1 true) (Wreath.mk c 1 true) := by
  obtain ⟨x,hx⟩ := isConj_iff.mp h
  exact isConj_iff.mpr ⟨⟨x,x,false⟩,by simp [hx]⟩

private theorem wRep_covers (w : W) : ∃ i, IsConj w (wRep i) := by
  obtain ⟨a,b,f⟩ := w
  cases f
  · have h := conj_base (h_can a) (h_can b)
    by_cases hh : hLabel a ≤ hLabel b
    · exact ⟨.inl ⟨(hLabel a,hLabel b),hh⟩,h⟩
    · exact ⟨.inl ⟨(hLabel b,hLabel a),le_of_not_ge hh⟩,h.trans (conj_swap _ _)⟩
  · exact ⟨.inr (hLabel (a*b)), (conj_flip_shape a b).trans (conj_flip_reduce (h_can (a*b)))⟩

private theorem classes_le : Nat.card (ConjClasses W) ≤ 35 := by
  have hs : Function.Surjective (ConjClasses.mk ∘ wRep) := by
    intro q
    obtain ⟨w,rfl⟩ := ConjClasses.mk_surjective q
    obtain ⟨i,hi⟩ := wRep_covers w
    exact ⟨i,ConjClasses.mk_eq_mk_iff_isConj.mpr hi.symm⟩
  have h := Nat.card_le_card_of_surjective (ConjClasses.mk ∘ wRep) hs
  have hI : Nat.card RepIndex = 35 := by
    rw [Nat.card_eq_fintype_card]
    decide
  exact hI ▸ h

private theorem comm_in_derived (x y : W) : x*y*x⁻¹*y⁻¹ ∈ commutator W := by
  change ⁅x,y⁆ ∈ commutator W
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)

private def derivedMap (x : H × ZMod 4) : W :=
  ⟨x.1, x.1⁻¹ * r (2 * (x.2.val : ZMod 8)), false⟩

private theorem derivedMap_mem (x : H × ZMod 4) : derivedMap x ∈ commutator W := by
  have hh1 := comm_in_derived ⟨x.1,1,false⟩ ⟨1,1,true⟩
  have hh1' : Wreath.mk x.1 x.1⁻¹ false ∈ commutator W := by simpa using hh1
  have hh2 := comm_in_derived ⟨1,sr 0,false⟩ ⟨1,r (-(x.2.val : ZMod 8)),false⟩
  have hh2' : Wreath.mk 1 (r (2 * (x.2.val : ZMod 8))) false ∈ commutator W := by
    simpa [two_mul] using hh2
  simpa [derivedMap] using (commutator W).mul_mem hh1' hh2'

private theorem derivedMap_inj : Function.Injective derivedMap := by
  rintro ⟨x,i⟩ ⟨y,j⟩ he
  have ha := congrArg Wreath.a he
  change x=y at ha
  subst y
  have hb := congrArg Wreath.b he
  change x⁻¹ * r (2 * (i.val : ZMod 8)) = x⁻¹ * r (2 * (j.val : ZMod 8)) at hb
  have hR := DihedralGroup.r.inj (mul_left_cancel hb)
  have hmod := congrArg ZMod.val hR
  have hv (z : ZMod 4) : (2 * (z.val : ZMod 8)).val = 2 * z.val := by
    rw [← Nat.cast_two, ← Nat.cast_mul, ZMod.val_natCast, Nat.mod_eq_of_lt]
    have := ZMod.val_lt z
    omega
  rw [hv i, hv j] at hmod
  have hij : i = j := ZMod.val_injective 4 (by omega)
  subst j
  rfl

private theorem derived_large : 64 ≤ Nat.card (commutator W) := by
  let f : H × ZMod 4 → commutator W := fun x => ⟨derivedMap x,derivedMap_mem x⟩
  have hinj : Function.Injective f := fun _ _ h => derivedMap_inj (congrArg Subtype.val h)
  have h := Nat.card_le_card_of_injective f hinj
  have hs : Nat.card (H × ZMod 4) = 64 := by
    rw [Nat.card_prod, DihedralGroup.nat_card, Nat.card_eq_fintype_card, ZMod.card]
  exact hs ▸ h

private theorem ab_small : Nat.card (Abelianization W) ≤ 8 := by
  have h := (commutator W).card_mul_index
  rw [w_card] at h
  change Nat.card (commutator W) * Nat.card (Abelianization W) = 512 at h
  have hle := Nat.mul_le_mul_right (Nat.card (Abelianization W)) derived_large
  omega

private theorem exponent_le : Monoid.exponent W ≤ 16 := by
  apply Nat.le_of_dvd (by decide)
  apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
  have h8 (a : H) : a^8 = 1 := by
    have h0 := Monoid.pow_exponent_eq_one a
    have he : Monoid.exponent H = 8 := DihedralGroup.exponent.trans (by decide)
    rwa [he] at h0
  have hp (a b : H) (n : ℕ) : (Wreath.mk a b false)^n = ⟨a^n,b^n,false⟩ := by
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ, ih, wf_mul, pow_succ, pow_succ]
  intro w
  obtain ⟨a,b,flip⟩ := w
  rw [show (16:ℕ) = 2*8 by decide, pow_mul, pow_two]
  cases flip <;> simp [hp,h8]
  all_goals rfl

private theorem w_pgroup : IsPGroup 2 W := IsPGroup.of_card (n := 9) w_card

/-- Exact conjecture #21, with absolute value on the integer difference. -/
def Conjecture21 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [Group.IsNilpotent G],
    |(Nat.card (commutator G) : ℤ) - Nat.card (Abelianization G)| + 1 ≤
      (Nat.card (ConjClasses G) : ℤ)

theorem graffiti3_conj21_false : ¬ Conjecture21 := by
  intro h
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  letI : Group.IsNilpotent W := w_pgroup.isNilpotent
  have hc := h W
  rw [abs_of_nonneg (by have := derived_large; have := ab_small; omega)] at hc
  have := derived_large
  have := ab_small
  have := classes_le
  omega

#print axioms graffiti3_conj21_false
end GraffitiThree2122
