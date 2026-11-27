import Rooted180

/-! The local normalization step for gluing arbitrary rooted blocks. All ranks
and the maximum eligible leaf count are computed on the given SimpleGraph. -/
set_option warningAsError true
namespace Rooted180
open Finset SimpleGraph Graffiti177
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

noncomputable def within (ok : Finset V → Prop) (S : Finset V) : ℕ := by
  classical exact (S.powerset.filter ok).sup card

omit [Fintype V] [DecidableEq V] in
private theorem within_le {ok : Finset V → Prop} {S X : Finset V} (h : X ⊆ S) (hx : ok X) :
    X.card ≤ within ok S := by
  classical exact le_sup (f := card) (mem_filter.mpr ⟨mem_powerset.mpr h,hx⟩)

omit [Fintype V] in
private theorem restrict_color {X : Finset V} (h : TwoColor G X) (B : Finset V) :
    TwoColor G (X ∩ B) := by
  obtain ⟨C,D,disj,eq,c,d⟩ := h
  refine ⟨C ∩ B,D ∩ B,disj.mono inter_subset_left inter_subset_left,?_,?_,?_⟩
  · rw [← eq]
    ext v
    simp only [mem_union,mem_inter]
    tauto
  · exact fun x hx y hy => c x (mem_inter.mp hx).1 y (mem_inter.mp hy).1
  · exact fun x hx y hy => d x (mem_inter.mp hx).1 y (mem_inter.mp hy).1

theorem restrict_bipartite (B : Finset V) :
    bipartiteNum G ≤ within (TwoColor G) B + (univ \ B).card := by
  classical
  apply Finset.sup_le
  intro X hx
  have small := within_le (inter_subset_right : X ∩ B ⊆ B)
    (restrict_color G (mem_filter.mp hx).2 B)
  have lost : X \ B ⊆ univ \ B := fun _ h => mem_sdiff.mpr ⟨mem_univ _,(mem_sdiff.mp h).2⟩
  have n := card_sdiff_add_card_inter X B
  have k := card_le_card lost
  omega

theorem restrict_leaves (S T : Finset V) :
    weightedLeaves G S ≤ weightedLeaves G T + (S \ T).card := by
  classical
  apply Finset.sup_le
  intro H h
  have b : (T ∩ leaves H).card ≤ weightedLeaves G T :=
    le_sup (f := fun J => (T ∩ leaves J).card) h
  have t : (S ∩ leaves H) ∩ T ⊆ T ∩ leaves H := by
    intro x hx
    exact mem_inter.mpr ⟨(mem_inter.mp hx).2,(mem_inter.mp (mem_inter.mp hx).1).2⟩
  have k : (S ∩ leaves H) \ T ⊆ S \ T := by
    intro x hx
    exact mem_sdiff.mpr ⟨(mem_inter.mp (mem_sdiff.mp hx).1).1,(mem_sdiff.mp hx).2⟩
  have n := card_sdiff_add_card_inter (S ∩ leaves H) T
  have t' := card_le_card t
  have k' := card_le_card k
  omega

def localBound (r : V) (P : Finset V) : Prop :=
  ∀ A : Finset V, Indep G A → 1+A.card+P.card ≤ weightedLeaves G (eligible A P r)+bipartiteNum G

/-- T is the set eligible for leaves in the block, C the vertices carrying
independence gain one, and B the vertices carrying bipartite gain one.
The root condition covers the three external cases: no independence weight
for r, odd external parity, or eligibility of r in the global root block. -/
theorem branch_transfer (r : V) (P T C B : Finset V) (h : localBound G r P)
    (root : r ∉ C ∨ r ∉ P ∨ r ∈ T) :
    1 + within (Indep G) C + P.card ≤
      weightedLeaves G T + within (TwoColor G) B + (univ \ B).card +
        (P.erase r \ T).card + (C \ insert r (T ∪ P)).card := by
  classical
  have empty : Indep G (∅ : Finset V) := by simp [Indep]
  obtain ⟨I,hi,eq⟩ := exists_mem_eq_sup (s := C.powerset.filter (Indep G)) (f := card)
    ⟨∅,mem_filter.mpr ⟨mem_powerset.mpr (empty_subset _),empty⟩⟩
  have sub := mem_powerset.mp (mem_filter.mp hi).1
  have estimate := h I (mem_filter.mp hi).2
  have cover : eligible I P r \ T ⊆ (P.erase r \ T) ∪ (C \ insert r (T ∪ P)) := by
    intro v hv
    obtain ⟨mem,out⟩ := mem_sdiff.mp hv
    have vw : v ∈ I ∪ P := by
      unfold eligible at mem
      split at mem
      · exact mem
      · exact mem_of_mem_erase mem
    have ne : v ≠ r := by
      rintro rfl
      unfold eligible at mem
      split at mem
      next both =>
        exact root.elim (fun hr => hr (sub both.1)) (fun h => h.elim (fun hr => hr both.2) out)
      next => exact (mem_erase.mp mem).1 rfl
    by_cases inP : v ∈ P
    · exact mem_union_left _ (mem_sdiff.mpr ⟨mem_erase.mpr ⟨ne,inP⟩,out⟩)
    · exact mem_union_right _ (mem_sdiff.mpr ⟨sub ((mem_union.mp vw).resolve_right inP),
        by simp [ne,out,inP]⟩)
  have loss := (card_le_card cover).trans (card_union_le _ _)
  have leaves := restrict_leaves G (eligible I P r) T
  have colors := restrict_bipartite G B
  change 1 + (C.powerset.filter (Indep G)).sup card + P.card ≤ _
  omega

/-- Two failing even copies at a common root refute 180 immediately, except
for one state where two parent bridges give a failing even state of cost zero. -/
theorem double_or_two_bridges (score da db : ℤ) (a0 : 0 ≤ da) (a1 : da ≤ 1)
    (b0 : 0 ≤ db) (b1 : db ≤ 1) (bad : score < 2-db) :
    2*score + db-da-2 < 0 ∨ (score=1 ∧ da=0 ∧ db=0) := by omega

#print axioms restrict_bipartite
#print axioms restrict_leaves
#print axioms branch_transfer
#print axioms double_or_two_bridges
end Rooted180

