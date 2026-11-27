import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Multiset.Sort

namespace Book567
open SimpleGraph Finset
variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
noncomputable def degreesDesc := (univ.val.map (fun v => G.degree v)).sort (· ≥ ·)
/-- The GraphCalc loop searches all prefix lengths from zero to the graph order,
and returns None if no prefix has a large enough degree sum. -/
noncomputable def subTotal? {U : Type*} [Fintype U] (G : SimpleGraph U) [DecidableRel G.Adj] :
    Option ℕ :=
  (List.range (Fintype.card U + 1)).find? fun k =>
    decide (Fintype.card U ≤ ((degreesDesc G).take k).sum)

theorem leaders (hn : 2 ≤ Fintype.card V) :
    ∃ (x : V) (b : ℕ) (l : List ℕ), degreesDesc G = G.degree x :: b :: l ∧
      (∀ y, G.degree y ≤ G.degree x) ∧ (∀ y, y ≠ x → G.degree y ≤ b) := by
  classical
  have len : (degreesDesc G).length = Fintype.card V := by simp [degreesDesc]
  obtain ⟨a,b,l,eqn⟩ : ∃ a b l, degreesDesc G = a :: b :: l := by
    cases hd : degreesDesc G with
    | nil => simp [hd] at len; omega
    | cons a l =>
      cases l with
      | nil => simp [hd] at len; omega
      | cons b l => exact ⟨a,b,l,rfl⟩
  have bag : ((a :: b :: l : List ℕ) : Multiset ℕ) = univ.val.map (G.degree ·) := by
    rw [← eqn, degreesDesc, Multiset.sort_eq]
  have memA : a ∈ univ.val.map (G.degree ·) := by rw [← bag]; simp
  obtain ⟨x, _, hx⟩ := Multiset.mem_map.mp memA
  subst a
  have sorted : (G.degree x :: b :: l).Pairwise (· ≥ ·) := by
    rw [← eqn]
    exact Multiset.sort_sorted _ _
  have maxHead {i : ℕ} {tail : List ℕ} (h : (i :: tail).Pairwise (· ≥ ·)) :
      ∀ k ∈ i :: tail, k ≤ i := by
    intro k hk
    rcases List.mem_cons.mp hk with rfl | hk
    · exact le_rfl
    · exact (List.pairwise_cons.mp h).1 _ hk
  refine ⟨x,b,l,eqn,?_,?_⟩
  · intro y
    apply maxHead sorted
    change G.degree y ∈ ((G.degree x :: b :: l : List ℕ) : Multiset ℕ)
    rw [bag]
    exact Multiset.mem_map.mpr ⟨y,mem_univ _,rfl⟩
  · intro y hy
    have rest : ((b :: l : List ℕ) : Multiset ℕ) =
        (univ.val.erase x).map (G.degree ·) := by
      apply (Multiset.cons_inj_right (G.degree x)).mp
      rw [← Multiset.map_cons (f := fun z => G.degree z), Multiset.cons_erase (s := univ.val) (mem_univ x)]
      exact bag
    apply maxHead (List.pairwise_cons.mp sorted).2
    change G.degree y ∈ ((b :: l : List ℕ) : Multiset ℕ)
    rw [rest]
    exact Multiset.mem_map.mpr ⟨y,(Multiset.mem_erase_of_ne hy).mpr (mem_univ _),rfl⟩

end Book567
