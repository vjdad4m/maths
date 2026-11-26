import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Lattice
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

/-! Ján Pastorek, AutoGraphForge normalized survivor line 353 (raw 369, ID 88eb33c4).
The affine orthogonal polarity construction uses the field of order 67.
All subset and component arguments are symbolic. -/
/- Matching definitions reproduced from Graffiti.pc #326. -/
namespace Graffiti326
open Finset SimpleGraph
open scoped BigOperators
set_option linter.unusedSectionVars false
noncomputable section
variable {V : Type*} [Fintype V]
local instance : DecidableEq V := Classical.decEq V
local instance (G : SimpleGraph V) : DecidableRel G.Adj := Classical.decRel G.Adj

def HasMatching (G : SimpleGraph V) (k : ℕ) :=
  ∃ f : Fin k × Bool ↪ V, ∀ i, G.Adj (f (i,false)) (f (i,true))

local instance (G : SimpleGraph V) : DecidablePred (HasMatching G) := Classical.decPred _

private def feasibleMatchingSizes (G : SimpleGraph V) : Finset ℕ :=
  (range (Fintype.card V / 2+1)).filter (HasMatching G)

private theorem matchingSizes_nonempty (G : SimpleGraph V) :
    (feasibleMatchingSizes G).Nonempty := by
  use 0
  simp only [feasibleMatchingSizes, mem_filter, mem_range]
  refine ⟨by omega, ⟨⟨fun p => Fin.elim0 p.1, ?_⟩, ?_⟩⟩
  · intro p; exact Fin.elim0 p.1
  · intro i; exact Fin.elim0 i

def matchingNumber (G : SimpleGraph V) : ℕ :=
  (feasibleMatchingSizes G).max' (matchingSizes_nonempty G)

theorem matchingNumber_attained (G : SimpleGraph V) : HasMatching G (matchingNumber G) := by
  exact (Finset.mem_filter.1 (Finset.max'_mem (feasibleMatchingSizes G)
    (matchingSizes_nonempty G))).2

end
end Graffiti326

/- Balanced separator definitions reproduced from AutoGraphForge line 379. -/
namespace AutoGraphForge379
open Finset SimpleGraph
open Classical
noncomputable section
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

/-- In the subgraph that remains, every component has at most half the
remaining order, rounded up. This includes the empty remaining graph. -/
def Balanced (R : Finset V) : Prop :=
  ∀ x : R, (univ.filter (fun y : R => (G.induce (R : Set V)).Reachable x y)).card ≤ (R.card + 1) / 2

/-- Minimize the number deleted over all balanced remaining graphs. -/
def wellSplitting : ℕ := sInf {k | ∃ R : Finset V, Balanced G R ∧ Rᶜ.card = k}

end
end AutoGraphForge379

namespace AutoGraphForge353
open Finset SimpleGraph
open scoped BigOperators
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
abbrev F := ZMod 67
instance : Fact (Nat.Prime 67) := ⟨by decide⟩
abbrev Q := {q : F // q ^ 33 = -1}
abbrev V := F × Q
abbrev Plane := F × F

theorem orderV : Fintype.card V = 2211 := by
  rw [Fintype.card_prod, ZMod.card]
  have h : Fintype.card Q = 33 := by decide
  omega

/-- At horizontal coordinate t, the polar of (s,q) has ordinate −(s−t)²−q.
Shearing the affine plane by a parabola changes these polars to straight lines. -/
def ordinate (a : V) (t : F) : F := -(a.1 - t)^2 - a.2.1

def graph : SimpleGraph V where
  Adj a b := a.2.1 + b.2.1 = -(a.1 - b.1)^2
  symm := by
    intro a b h
    change _ + _ = _ at h ⊢
    linear_combination h
  loopless := by
    intro a h
    change a.2.1 + a.2.1 = -(a.1 - a.1)^2 at h
    have z : (2:F) * a.2.1 = 0 := by linear_combination h
    have az := (mul_eq_zero.mp z).resolve_left (by decide)
    have key := a.2.2
    rw [az] at key
    norm_num at key

private theorem norm_of_triangle {a b c : V} (hab : graph.Adj a b)
    (hbc : graph.Adj b c) (hac : graph.Adj a c) :
    a.2.1 = -(a.1-b.1)*(a.1-c.1) := by
  change _ + _ = _ at hab hbc hac
  have h : (2:F) * (a.2.1 + (a.1-b.1)*(a.1-c.1)) = 0 := by
    linear_combination hab + hac - hbc
  have e := (mul_eq_zero.mp h).resolve_left (by decide)
  linear_combination e

theorem triangleFree : graph.CliqueFree 3 := by
  intro S hs
  obtain ⟨a,b,c,ha,hb,hc,ab,ac,bc⟩ := two_lt_card_iff.mp (show 2 < S.card by rw [hs.card_eq]; decide)
  have x := hs.isClique ha hb ab
  have y := hs.isClique hb hc bc
  have z := hs.isClique ha hc ac
  let t := (a.1-b.1)*(b.1-c.1)*(c.1-a.1)
  have eq : a.2.1*b.2.1*c.2.1 = t^2 := by
    rw [norm_of_triangle x y z, norm_of_triangle x.symm z y, norm_of_triangle z.symm x y.symm]
    dsimp [t]
    ring
  have non : ∀ v : F, v^66 ≠ -1 := by decide
  apply non t
  calc t^66 = (t^2)^33 := by rw [← pow_mul]
       _ = _ := by rw [← eq, mul_pow, mul_pow, a.2.2, b.2.2, c.2.2]; ring

private def weight (a : V) (w : Plane) : ℕ := if w.2 = ordinate a w.1 then 1 else 0

private theorem line_size (a : V) : ∑ w : Plane, weight a w = 67 := by
  rw [Fintype.sum_prod_type]
  simp [weight, ZMod.card]

private theorem unique_intersection {a b : V} (hne : a ≠ b) {s t : F}
    (hs : ordinate a s = ordinate b s) (ht : ordinate a t = ordinate b t) : s = t := by
  unfold ordinate at hs ht
  have e : (2 : F) * ((a.1-b.1)*(s-t)) = 0 := by linear_combination hs - ht
  rcases mul_eq_zero.mp ((mul_eq_zero.mp e).resolve_left (by decide)) with h | h
  · have slopes := sub_eq_zero.mp h
    rw [slopes] at hs
    have intercept : a.2.1 = b.2.1 := by linear_combination -hs
    exact (hne (Prod.ext slopes (Subtype.ext intercept))).elim
  · exact sub_eq_zero.mp h

private theorem pair_sum (a b : V) :
    ∑ w : Plane, weight a w * weight b w ≤ (if b = a then 66 else 0) + 1 := by
  classical
  by_cases e : b = a
  · subst b
    have reduce (w : Plane) : weight a w * weight a w = weight a w := by
      unfold weight
      split <;> decide
    simp_rw [reduce]
    simp [line_size]
  · rw [if_neg e, zero_add]
    let P (w : Plane) := w.2 = ordinate a w.1 ∧ w.2 = ordinate b w.1
    have reduce (w : Plane) : weight a w * weight b w = if P w then 1 else 0 := by
      by_cases h : w.2 = ordinate a w.1 <;> by_cases j : w.2 = ordinate b w.1 <;> simp [P,weight,h,j]
    simp_rw [reduce]
    rw [sum_boole]
    apply card_le_one.mpr
    intro w hw v hv
    have hw' : P w := (mem_filter.mp hw).2
    have hv' : P v := (mem_filter.mp hv).2
    have first := unique_intersection (Ne.symm e) (hw'.1.symm.trans hw'.2) (hv'.1.symm.trans hv'.2)
    exact Prod.ext first (hw'.1.trans ((congrArg (ordinate a) first).trans hv'.1.symm))

private def degree (A : Finset V) (w : Plane) := ∑ a ∈ A, weight a w

private theorem first_moment (A : Finset V) : ∑ w, degree A w = A.card * 67 := by
  unfold degree
  rw [sum_comm]
  simp [line_size]

private theorem second_moment (A : Finset V) :
    ∑ w, (degree A w)^2 ≤ A.card * (A.card + 66) := by
  classical
  have expand (w : Plane) : (degree A w)^2 = ∑ a ∈ A, ∑ b ∈ A, weight a w * weight b w := by
    simp_rw [degree, pow_two, sum_mul, mul_sum]
  simp_rw [expand]
  rw [sum_comm]
  calc
    _ = ∑ a ∈ A, ∑ b ∈ A, ∑ w : Plane, weight a w * weight b w := by
      apply sum_congr rfl
      intro a _
      exact sum_comm
    _ ≤ ∑ a ∈ A, ∑ b ∈ A, ((if b = a then 66 else 0) + 1) := by
      exact sum_le_sum fun a _ => sum_le_sum fun b _ => pair_sum a b
    _ = _ := by simp [sum_add_distrib, Nat.add_comm, Nat.mul_add]

private def point : V ↪ Plane where
  toFun a := (a.1,a.2.1)
  inj' := fun _ _ h => Prod.ext (congrArg (fun p : Plane => p.1) h) (Subtype.ext (congrArg (fun p : Plane => p.2) h))

private theorem incidence_bound (A B : Finset V) (hA : 0 < A.card)
    (anti : ∀ a ∈ A, ∀ b ∈ B, ¬graph.Adj a b) :
    B.card * (A.card + 66) ≤ 4489 * 66 := by
  classical
  let T := (B.map point)ᶜ
  have plane_card : Fintype.card Plane = 4489 := by rw [Fintype.card_prod, ZMod.card]
  have sizeT : T.card + B.card = 4489 := by
    have h := card_add_card_compl (B.map point)
    simp only [card_map, plane_card] at h
    dsimp [T]
    omega
  have vanishes (w : Plane) (hw : w ∉ T) : degree A w = 0 := by
    have hm : w ∈ B.map point := by simpa [T] using hw
    obtain ⟨b,hb,rfl⟩ := mem_map.mp hm
    apply sum_eq_zero
    intro a ha
    have no : b.2.1 ≠ ordinate a b.1 := by
      intro e
      apply anti a ha b hb
      change _ + _ = _
      unfold ordinate at e
      linear_combination e
    exact if_neg no
  have first : ∑ w ∈ T, degree A w = A.card * 67 :=
    (sum_subset (subset_univ T) (fun w _ hw => vanishes w hw)).trans (first_moment A)
  have second : ∑ w ∈ T, (degree A w)^2 ≤ A.card * (A.card + 66) :=
    (sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)).trans (second_moment A)
  have cs := sum_mul_sq_le_sq_mul_sq T (fun _ => (1:ℕ)) (degree A)
  simp only [one_mul, one_pow, sum_const, Nat.nsmul_eq_mul, mul_one] at cs
  rw [first] at cs
  have bounds : A.card * (A.card*4489) ≤ A.card * (T.card * (A.card+66)) := calc
    _ = (A.card*67)^2 := by ring
    _ ≤ T.card * ∑ w ∈ T, (degree A w)^2 := cs
    _ ≤ T.card * (A.card*(A.card+66)) := Nat.mul_le_mul_left _ second
    _ = _ := by ring
  have h := Nat.le_of_mul_le_mul_left bounds hA
  nlinarith only [h, congrArg (fun n : ℕ => n * (A.card+66)) sizeT]

open Classical in
private theorem balanced_split {U : Type*} [Fintype U] (H : SimpleGraph U)
    (size : 1106 ≤ Fintype.card U)
    (bal : ∀ x : U, (univ.filter (fun y : U => H.Reachable x y)).card ≤ (Fintype.card U+1)/2) :
    ∃ S : Finset U, 368 ≤ S.card ∧ 368 ≤ Fintype.card U - S.card ∧
      ∀ a ∈ S, ∀ b ∉ S, ¬H.Adj a b := by
  classical
  let comp (x : U) := univ.filter (fun y : U => H.Reachable x y)
  let closed (S : Finset U) := ∀ x ∈ S, ∀ y, H.Reachable x y → y ∈ S
  have component (x : U) : closed (comp x) := by
    intro a ha b hab
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp ha).2.trans hab⟩
  have finish (S : Finset U) (lo : 368 ≤ S.card) (hi : 368 ≤ Fintype.card U - S.card)
      (cl : closed S) : ∃ T : Finset U, 368 ≤ T.card ∧ 368 ≤ Fintype.card U - T.card ∧
      ∀ a ∈ T, ∀ b ∉ T, ¬H.Adj a b :=
    ⟨S,lo,hi,fun a ha b hb edge => hb (cl a ha b edge.reachable)⟩
  by_cases big : ∃ x : U, 368 ≤ (comp x).card
  · obtain ⟨x,hx⟩ := big
    have h := bal x
    change (comp x).card ≤ _ at h
    exact finish _ hx (by omega) (component x)
  push_neg at big
  let options := univ.powerset.filter (fun S : Finset U => closed S ∧ S.card < 368)
  have member (S : Finset U) : S ∈ options ↔ closed S ∧ S.card < 368 := by simp [options]
  have empty : (∅ : Finset U) ∈ options :=
    (member _).mpr ⟨fun _ hx => (not_mem_empty _ hx).elim, by simp⟩
  obtain ⟨S,hS,hmax⟩ := exists_max_image options Finset.card ⟨∅,empty⟩
  obtain ⟨sc,small⟩ := (member S).mp hS
  obtain ⟨x,hx⟩ : ∃ x : U, x ∉ S := by
    by_contra hex
    push_neg at hex
    have eq : S = univ := eq_univ_of_forall hex
    rw [eq,card_univ] at small
    omega
  let T := S ∪ comp x
  have tc : closed T := by
    intro a ha b hab
    rcases mem_union.mp ha with h | h
    · exact mem_union_left _ (sc a h b hab)
    · exact mem_union_right _ (component x a h b hab)
  have grow : S.card < T.card := by
    apply card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨subset_union_left, ?_⟩
    intro eq
    have xt : x ∈ T := mem_union_right _ (mem_filter.mpr ⟨mem_univ _, Reachable.refl _⟩)
    exact hx (eq.symm ▸ xt)
  have low : 368 ≤ T.card := by
    by_contra hlow
    have lt := Nat.lt_of_not_ge hlow
    exact (Nat.not_le_of_lt grow) (hmax T ((member _).mpr ⟨tc,lt⟩))
  have bound := card_union_le S (comp x)
  have smallx := big x
  change T.card ≤ _ at bound
  exact finish T low (by omega) tc

private theorem too_large (A B : Finset V) (ha : 368 ≤ A.card) (hb : 368 ≤ B.card)
    (total : 1106 ≤ A.card + B.card) (anti : ∀ a ∈ A, ∀ b ∈ B, ¬graph.Adj a b) : False := by
  have impossible (m b : ℕ) (small : 368 ≤ m) (large : 368 ≤ b) (sum : 1106 ≤ m+b)
      (sorted : m ≤ b) (bound : b*(m+66) ≤ 4489*66) : False := by
    have half : 553 ≤ b := by omega
    obtain ⟨i,hi⟩ := Nat.exists_eq_add_of_le small
    obtain ⟨j,hj⟩ := Nat.exists_eq_add_of_le large
    subst m b
    nlinarith only [Nat.zero_le (i*j), sum, half, bound]
  rcases le_total A.card B.card with h | h
  · exact impossible _ _ ha hb total h (incidence_bound A B (by omega) anti)
  · exact impossible _ _ hb ha (by omega) h (incidence_bound B A (by omega)
      (fun b hb' a ha' e => anti a ha' b hb' e.symm))

open AutoGraphForge379 Graffiti326
private theorem attaining {U : Type*} [Fintype U] (G : SimpleGraph U) :
    ∃ R : Finset U, Balanced G R ∧ Fintype.card U - R.card = wellSplitting G := by
  classical
  have empty : Balanced G ∅ := fun x => False.elim (not_mem_empty _ x.2)
  have ex : {k | ∃ R : Finset U, Balanced G R ∧ Rᶜ.card = k}.Nonempty :=
    ⟨_,∅,empty,rfl⟩
  obtain ⟨R,bal,cost⟩ := Nat.sInf_mem ex
  change Rᶜ.card = wellSplitting G at cost
  exact ⟨R, bal, by rwa [card_compl] at cost⟩

theorem wellSplitting_lower : 1106 ≤ wellSplitting graph := by
  classical
  obtain ⟨R,bal,cost⟩ := attaining graph
  rw [orderV] at cost
  by_contra fail
  have rlarge : 1106 ≤ Fintype.card R := by rw [Fintype.card_coe]; omega
  let H := graph.induce (R : Set V)
  obtain ⟨S,hs,hc,anti⟩ := balanced_split (U := R) H rlarge (by
    intro x
    rw [Fintype.card_coe]
    exact bal x)
  let emb : R ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  apply too_large (S.map emb) (Sᶜ.map emb)
  · simpa using hs
  · simpa [card_compl] using hc
  · simpa only [card_map, card_add_card_compl] using rlarge
  · intro a ha b hb e
    obtain ⟨x,hx,rfl⟩ := mem_map.mp ha
    obtain ⟨y,hy,rfl⟩ := mem_map.mp hb
    exact anti x hx y (mem_compl.mp hy) e

theorem matching_upper : matchingNumber graph ≤ 1105 := by
  obtain ⟨f,_⟩ := matchingNumber_attained graph
  have h := Fintype.card_le_of_injective f f.injective
  rw [orderV, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool] at h
  omega

/-- The pinned normalized statement has only nontriviality and triangle-freeness as
hypotheses. Its right side is maximum matching cardinality. -/
theorem counterexample_line353 : 2 ≤ Fintype.card V ∧ graph.CliqueFree 3 ∧
    ¬wellSplitting graph ≤ matchingNumber graph :=
  ⟨by rw [orderV]; decide, triangleFree, by have := wellSplitting_lower; have := matching_upper; omega⟩

#print axioms orderV
#print axioms triangleFree
#print axioms wellSplitting_lower
#print axioms matching_upper
#print axioms counterexample_line353
end AutoGraphForge353

