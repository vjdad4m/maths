import FourthDegree
import Mathlib.Data.Finset.Union

namespace UnionClosedBoundary
open Finset
open scoped BigOperators
variable {V : Type*} [DecidableEq V]

/-- A union of a finite collection of patterns omitting k still belongs
to the family if the patterns omitting k are closed under binary unions. -/
private theorem biUnion_mem_avoiding (C : Finset (Finset V)) (k : V)
    (bot : ∅ ∈ C)
    (ucl : ∀ A ∈ C, ∀ B ∈ C, k ∉ A → k ∉ B → A ∪ B ∈ C)
    (I : Finset V) (K : V → Finset V)
    (hm : ∀ i ∈ I, K i ∈ C ∧ k ∉ K i) :
    I.biUnion K ∈ C ∧ k ∉ I.biUnion K := by
  induction I using Finset.induction_on with
  | empty => simpa using bot
  | @insert i I hi ih =>
    obtain ⟨hc,hn⟩ := hm i (mem_insert_self _ _)
    obtain ⟨hd,ho⟩ := ih (fun j hj => hm j (mem_insert_of_mem hj))
    rw [biUnion_insert]
    exact ⟨ucl _ hc _ hd hn ho, fun h => (mem_union.mp h).elim hn ho⟩

/-- Delete the entire block equivalent to a coordinate of largest core.
The image is the union of the other coordinates' cores. Only union
closure on the slice of patterns omitting the chosen coordinate is needed. -/
theorem lattice_core_injection [Fintype V]
    (C : Finset (Finset V)) (bot : ∅ ∈ C)
    (K : V → Finset V) (core : ∀ i, IsCore C i (K i))
    (k : V) (maxK : ∀ i, (K i).card ≤ (K k).card)
    (ucl : ∀ A ∈ C, ∀ B ∈ C, k ∉ A → k ∉ B → A ∪ B ∈ C)
    (T : Finset V) : (omits C k T).card ≤ (contains C k T).card := by
  classical
  let D := (univ : Finset V).filter fun i => k ∈ K i
  have rem (S : Finset V) (hS : S ∈ C) : S \ D ∈ C ∧ k ∉ S \ D := by
    have hm (i : V) (hi : i ∈ S \ D) : K i ∈ C ∧ k ∉ K i := by
      refine ⟨(core i).1,fun h => (mem_sdiff.mp hi).2 ?_⟩
      exact mem_filter.mpr ⟨mem_univ _,h⟩
    have e : (S \ D).biUnion K = S \ D := by
      ext j
      constructor
      · intro hj
        obtain ⟨i,hi,hji⟩ := mem_biUnion.mp hj
        have subS := (core i).2.2 S hS (mem_sdiff.mp hi).1
        refine mem_sdiff.mpr ⟨subS hji,fun hD => (hm i hi).2 ?_⟩
        exact (core j).2.2 _ (core i).1 hji ((mem_filter.mp hD).2)
      · intro hj
        exact mem_biUnion.mpr ⟨j,hj,(core j).2.1⟩
    rw [← e]
    exact biUnion_mem_avoiding C k bot ucl _ K hm
  have dsub (S : Finset V) (hS : S ∈ C) (hkS : k ∈ S) : D ⊆ S := by
    intro i hi
    have sub : K k ⊆ K i := (core k).2.2 _ (core i).1 (mem_filter.mp hi).2
    have e := eq_of_subset_of_card_le sub (maxK i)
    exact (core k).2.2 S hS hkS (e.symm ▸ (core i).2.1)
  apply card_le_card_of_injOn (fun S : Finset V => S \ D)
  · intro S hS
    obtain ⟨hSC,sub,_⟩ := mem_filter.mp hS
    exact mem_filter.mpr ⟨(rem S hSC).1,sdiff_subset.trans sub,(rem S hSC).2⟩
  · intro S hS U hU e
    obtain ⟨hSC,_,hkS⟩ := mem_filter.mp hS
    obtain ⟨hUC,_,hkU⟩ := mem_filter.mp hU
    calc
      S = S \ D ∪ D := (sdiff_union_of_subset (dsub S hSC hkS)).symm
      _ = U \ D ∪ D := congrArg (· ∪ D) e
      _ = U := sdiff_union_of_subset (dsub U hUC hkU)

#print axioms lattice_core_injection

theorem lattice_pointwise [Fintype V] [Nonempty V]
    (C : Finset (Finset V)) (bot : ∅ ∈ C) (cl : InterClosed C)
    (ucl : ∀ A ∈ C, ∀ B ∈ C, A ∪ B ∈ C) :
    ∃ k : V, ∀ T : Finset V, (omits C k T).card ≤ (contains C k T).card := by
  classical
  by_cases occ : ∀ k : V, ∃ S ∈ C, k ∈ S
  · choose K core using fun k => core_exists cl k (occ k)
    obtain ⟨k,_,hmax⟩ := (univ : Finset V).exists_max_image (fun i => (K i).card) univ_nonempty
    exact ⟨k,lattice_core_injection C bot K core k (fun i => hmax i (mem_univ _))
      (fun A ha B hb _ _ => ucl A ha B hb)⟩
  · obtain ⟨k,nk⟩ := not_forall.mp occ
    refine ⟨k,fun T => ?_⟩
    have eq : omits C k T = ∅ := eq_empty_iff_forall_not_mem.mpr fun S hs =>
      nk ⟨S,(mem_filter.mp hs).1,(mem_filter.mp hs).2.2⟩
    simp [eq]

/-- Phan's comparison at every degree for families closed under both
unions and intersections. The same coordinate works for all monomials. -/
theorem phan_lattice [Fintype V] [Nonempty V]
    (F : Finset (Finset V)) (top : (univ : Finset V) ∈ F)
    (ucl : ∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F)
    (icl : ∀ A ∈ F, ∀ B ∈ F, A ∩ B ∈ F)
    (m : ℕ) (x : V → ℝ) (hx : ∀ i, 0 ≤ x i) :
    ∃ k : V,
      (∑ A ∈ F.filter (fun A => k ∉ A), ∑ B ∈ A.powersetCard m, ∏ i ∈ B, x i) ≤
      ∑ A ∈ F.filter (fun A => k ∈ A), ∑ B ∈ (A.erase k).powersetCard m, ∏ i ∈ B, x i := by
  apply phan_of_coefficients F m x
  have bot : ∅ ∈ F.image compl := mem_image.mpr ⟨univ,top,compl_univ⟩
  have cc : InterClosed (F.image compl) := by
    intro S hS T hT
    obtain ⟨A,hA,rfl⟩ := mem_image.mp hS
    obtain ⟨B,hB,rfl⟩ := mem_image.mp hT
    exact mem_image.mpr ⟨A ∪ B,ucl A hA B hB,compl_union A B⟩
  have uc : ∀ S ∈ F.image compl, ∀ T ∈ F.image compl, S ∪ T ∈ F.image compl := by
    intro S hS T hT
    obtain ⟨A,hA,rfl⟩ := mem_image.mp hS
    obtain ⟨B,hB,rfl⟩ := mem_image.mp hT
    exact mem_image.mpr ⟨A ∩ B,icl A hA B hB,compl_inter A B⟩
  obtain ⟨k,hk⟩ := lattice_pointwise (F.image compl) bot cc uc
  refine ⟨k,sum_le_sum (fun B _ => mul_le_mul_of_nonneg_left ?_ (prod_nonneg fun i _ => hx i))⟩
  have c : (absent F k B).card ≤ (present F k B).card := by
    by_cases b : k ∈ B
    · have e : absent F k B = ∅ := eq_empty_iff_forall_not_mem.mpr fun A ha =>
        (mem_filter.mp ha).2.2 ((mem_filter.mp ha).2.1 b)
      simp [e]
    · rw [← count_absent,← count_present F k B b]
      exact hk Bᶜ
  exact_mod_cast c

#print axioms lattice_pointwise
#print axioms phan_lattice
end UnionClosedBoundary
