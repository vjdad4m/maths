/-
Proof of Davila Graffiti³ #25. Every nonidentity coset of the commutator subgroup supplies a class; inside that subgroup the nonempty derived-series layers and the identity supply the remaining distinct classes.
Source: Randy Davila, Graffiti³ (Research Square v1), https://doi.org/10.21203/rs.3.rs-8493329/v1
Reproduce in a project pinned to Lean 4.19.0 and Mathlib v4.19.0 with lake env lean.
AI-assisted work shared for review; this is not a claim of priority.
-/

import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Abelianization
import Mathlib.Algebra.Group.ConjFinite
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.ByContra

namespace GraffitiThree25
set_option maxHeartbeats 1000000
variable {G : Type*} [Group G]

private lemma step_le (j : ℕ) : derivedSeries G (j+1) ≤ derivedSeries G j := by
  letI := derivedSeries_normal G j
  rw [derivedSeries_succ]
  exact Subgroup.commutator_le_left _ _

private lemma descending : Antitone (derivedSeries G) :=
  antitone_nat_of_succ_le (fun j => step_le j)

private lemma layer_nonempty (d j : ℕ) (hd : derivedSeries G d = ⊥)
    (hmin : ∀ i < d, derivedSeries G i ≠ ⊥) (hj : j < d) :
    ∃ x : G, x ∈ derivedSeries G j ∧ x ∉ derivedSeries G (j+1) := by
  have hne : derivedSeries G j ≠ derivedSeries G (j+1) := by
    intro hEq
    have hi (k : ℕ) : derivedSeries G (j+k) = derivedSeries G j := by
      induction k with
      | zero => simp
      | succ k ih =>
        rw [Nat.add_succ, derivedSeries_succ, ih, ← derivedSeries_succ, ← hEq]
    obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le (show j ≤ d by omega)
    exact hmin j hj ((hi e).symm.trans (he ▸ hd))
  by_contra! h
  exact hne (le_antisymm (fun _ hx => h _ hx) (step_le j))

private lemma normal_conj_iff (j : ℕ) {x y : G} (h : IsConj x y) :
    x ∈ derivedSeries G j ↔ y ∈ derivedSeries G j := by
  have hh {a b : G} (hab : IsConj a b) (ha : a ∈ derivedSeries G j) :
      b ∈ derivedSeries G j := by
    obtain ⟨g, rfl⟩ := isConj_iff.mp hab
    exact (derivedSeries_normal G j).conj_mem a ha g
  exact ⟨hh h, hh h.symm⟩

noncomputable def abClass : ConjClasses G → Abelianization G :=
  Quotient.lift (fun x => Abelianization.of x)
    (fun _ _ h => isConj_iff_eq.mp (Abelianization.of.map_isConj h))

@[simp] lemma abClass_mk (x : G) : abClass (ConjClasses.mk x) = Abelianization.of x := rfl

private lemma abClass_surj : Function.Surjective (@abClass G _) := by
  intro q
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective q
  exact ⟨ConjClasses.mk x, hx⟩

private lemma abClass_of_mem {x : G} (j : ℕ) (hj : 1 ≤ j) (hx : x ∈ derivedSeries G j) :
    abClass (ConjClasses.mk x) = 1 := by
  have hm : x ∈ derivedSeries G 1 := descending hj hx
  rw [derivedSeries_one, ← Abelianization.ker_of] at hm
  exact hm

private lemma card_ab_le [Finite G] : Nat.card (Abelianization G) ≤ Nat.card (ConjClasses G) :=
  Nat.card_le_card_of_surjective abClass abClass_surj

private theorem card_bound [Finite G] (d : ℕ) (hd : derivedSeries G d = ⊥)
    (hmin : ∀ i < d, derivedSeries G i ≠ ⊥) :
    Nat.card (Abelianization G) + (d-1) ≤ Nat.card (ConjClasses G) := by
  classical
  let base (q : Abelianization G) : ConjClasses G :=
    if q = 1 then ConjClasses.mk 1 else (abClass_surj q).choose
  have hbase (q : Abelianization G) : abClass (base q) = q := by
    by_cases h : q=1
    · simp [base,h]
    · simpa [base,h] using (abClass_surj q).choose_spec
  have hlay (i : Fin (d-1)) :
      ∃ x : G, x ∈ derivedSeries G (i.val+1) ∧ x ∉ derivedSeries G (i.val+2) :=
    layer_nonempty d (i.val+1) hd hmin (by omega)
  let layer (i : Fin (d-1)) : G := (hlay i).choose
  have hmem (i : Fin (d-1)) :
      layer i ∈ derivedSeries G (i.val+1) ∧ layer i ∉ derivedSeries G (i.val+2) :=
    (hlay i).choose_spec
  let F : Abelianization G ⊕ Fin (d-1) → ConjClasses G :=
    Sum.elim base (fun i => ConjClasses.mk (layer i))
  have hinj : Function.Injective F := by
    intro a b h
    have mixed (q : Abelianization G) (i : Fin (d-1)) :
        base q ≠ ConjClasses.mk (layer i) := by
      intro he
      have heq := congrArg abClass he
      rw [hbase, abClass_of_mem _ (by omega) (hmem i).1] at heq
      have hconj : IsConj (layer i) (1:G) := by
        apply ConjClasses.mk_eq_mk_iff_isConj.mp
        simpa [base,heq] using he.symm
      have hz := isConj_one_left.mp hconj
      exact (hmem i).2 (hz ▸ (derivedSeries G (i.val+2)).one_mem)
    cases a with
    | inl q =>
      cases b with
      | inl r =>
        have hq := congrArg abClass h
        change abClass (base q) = abClass (base r) at hq
        rw [hbase, hbase] at hq
        exact congrArg Sum.inl hq
      | inr j => exact False.elim (mixed q j h)
    | inr i =>
      cases b with
      | inl q => exact False.elim (mixed q i h.symm)
      | inr j =>
        have hc := ConjClasses.mk_eq_mk_iff_isConj.mp h
        apply congrArg Sum.inr
        apply Fin.ext
        by_contra! hh
        obtain hij | hji := lt_or_gt_of_ne hh
        · exact (hmem i).2 ((normal_conj_iff _ hc).mpr
              (descending (by omega : i.val+2 ≤ j.val+1) (hmem j).1))
        · exact (hmem j).2 ((normal_conj_iff _ hc).mp
              (descending (by omega : j.val+2 ≤ i.val+1) (hmem i).1))
  simpa using Nat.card_le_card_of_injective F hinj

noncomputable def derivedLength (G : Type*) [Group G] : ℤ := by
  classical
  exact if h : ∃ n, derivedSeries G n = ⊥ then (Nat.find h : ℤ) else -1

/-- Exact Graffiti³ #25 in terms of Mathlib's conjugacy classes, abelianization
and derived series, with the stated nonsolvable convention. -/
theorem graffiti3_conj25 (G : Type*) [Group G] [Finite G] :
    (Nat.card (Abelianization G) : ℤ) + derivedLength G - 1 ≤
      (Nat.card (ConjClasses G) : ℤ) := by
  classical
  unfold derivedLength
  split
  · rename_i hs
    have hb := card_bound (Nat.find hs) (Nat.find_spec hs) (fun i hi => Nat.find_min hs hi)
    omega
  · have h := card_ab_le (G := G)
    omega

#print axioms graffiti3_conj25
end GraffitiThree25
