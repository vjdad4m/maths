import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Order.Interval.Finset.Nat
import Lean.Elab.Tactic.Omega

/-!
Pure finite arithmetic for the crossing case in Pósa's circumference argument.
Source draft only; not yet checked by Lean.
-/
namespace PosaCrossing189

open Finset

/-- For a spine indexed from 0 to N, the chords from 0 to i and from N
to j with j < i allow a cycle with this set of spine indices. -/
def kept (N j i : ℕ) : Finset ℕ := Icc 0 j ∪ Icc i N

theorem mem_kept {N j i x : ℕ} :
    x ∈ kept N j i ↔ x ≤ j ∨ (i ≤ x ∧ x ≤ N) := by
  simp [kept, Finset.mem_Icc]

/-- If two endpoint-neighbor sets cross, a minimum positive gap gives
a cycle using at least their combined cardinality. The conclusion
also gives the gap witness and the two pivot indices. -/
theorem exists_min_gap_card_kept {N : ℕ} {L R : Finset ℕ}
    (left : ∀ i ∈ L, 0 < i ∧ i < N)
    (right : ∀ j ∈ R, 0 < j ∧ j < N)
    (disj : Disjoint (L.image (fun i => i - 1)) R)
    (cross : ∃ i ∈ L, ∃ j ∈ R, j < i) :
    ∃ i ∈ L, ∃ j ∈ R, j < i ∧
      (∀ i' ∈ L, ∀ j' ∈ R, j' < i' → i - j ≤ i' - j') ∧
      L.card + R.card ≤ (kept N j i).card := by
  let X : Finset (ℕ × ℕ) := (L ×ˢ R).filter (fun p => p.2 < p.1)
  have inX {i j : ℕ} (il : i ∈ L) (jr : j ∈ R) (ji : j < i) : (i, j) ∈ X :=
    Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨il, jr⟩, ji⟩
  have hX : X.Nonempty := by
    obtain ⟨i, il, j, jr, ji⟩ := cross
    exact ⟨(i,j), inX il jr ji⟩
  obtain ⟨⟨i,j⟩, hmem, hmin⟩ := Finset.exists_min_image X (fun p => p.1 - p.2) hX
  have dat : (i ∈ L ∧ j ∈ R) ∧ j < i := by
    simpa only [X, Finset.mem_filter, Finset.mem_product] using hmem
  obtain ⟨⟨il, jr⟩, ji⟩ := dat
  have minimal (u : ℕ) (ul : u ∈ L) (v : ℕ) (vr : v ∈ R) (vu : v < u) :
      i - j ≤ u - v :=
    hmin (u,v) (inX ul vr vu)
  refine ⟨i, il, j, jr, ji, minimal, ?_⟩
  let L' := L.image (fun x => x - 1)
  have full : L'.card = L.card := by
    apply Finset.card_image_of_injOn
    intro u hu v hv uv
    have hu' := (left u hu).1
    have hv' := (left v hv).1
    change u - 1 = v - 1 at uv
    omega
  have predMem : i - 1 ∈ L' := Finset.mem_image.mpr ⟨i, il, rfl⟩
  have ik := (left i il).2
  let A := L'.erase (i - 1)
  have Ato : A ⊆ kept N j i := by
    intro x hx
    obtain ⟨hne, hm⟩ := Finset.mem_erase.mp hx
    obtain ⟨u, ul, rfl⟩ := Finset.mem_image.mp hm
    have ui : u ≠ i := by
      intro e
      exact hne (congrArg (fun z : ℕ => z - 1) e)
    have out : u ≤ j ∨ i < u := by
      by_contra bad
      have uj : j < u := by omega
      have := minimal u ul j jr uj
      omega
    have un := (left u ul).2
    exact mem_kept.mpr (by omega)
  have Rto : R ⊆ kept N j i := by
    intro x xr
    have out : x ≤ j ∨ i ≤ x := by
      by_contra bad
      have xi : x < i := by omega
      have := minimal i il x xr xi
      omega
    have xn := (right x xr).2
    exact mem_kept.mpr (by omega)
  have sep : Disjoint A R :=
    Finset.disjoint_left.mpr (fun _ hx => Finset.disjoint_left.mp disj (Finset.mem_erase.mp hx).2)
  have nfree : N ∉ A ∪ R := by
    intro h
    rcases Finset.mem_union.mp h with hA | hR
    · obtain ⟨u, ul, eq⟩ := Finset.mem_image.mp ((Finset.mem_erase.mp hA).2)
      have un := (left u ul).2
      omega
    · exact (lt_irrefl N) ((right N hR).2)
  have incl : insert N (A ∪ R) ⊆ kept N j i := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact mem_kept.mpr (Or.inr ⟨ik.le, le_rfl⟩)
    · exact (Finset.mem_union.mp hx).elim (fun h => Ato h) (fun h => Rto h)
  have count : A.card + 1 = L.card := by
    exact (Finset.card_erase_add_one predMem).trans full
  have le := Finset.card_le_card incl
  rw [Finset.card_insert_of_not_mem nfree, Finset.card_union_of_disjoint sep] at le
  omega

end PosaCrossing189

#print axioms PosaCrossing189.exists_min_gap_card_kept
