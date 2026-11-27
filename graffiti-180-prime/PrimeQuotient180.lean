import PinnedPrime180

set_option warningAsError true
namespace Minimal180.Substitution
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
open Classical
variable {V B : Type*} [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]
variable {H : SimpleGraph V} {G : SimpleGraph B} {f : V→B}

omit [DecidableEq V] [Fintype B] in
theorem Bags.modulePull (h : Bags H G f) (K : Finset B) (hom : Homogeneous G K) :
    Homogeneous H (pull f K) := by
  intro x out a am b bm
  have no : f x∉K := fun z => out (mem_pull.mpr z)
  have aK := mem_pull.mp am
  have bK := mem_pull.mp bm
  exact (h.across (x:=x) (y:=a) (fun e => no (e ▸ aK))).trans
    ((hom _ no _ aK _ bK).trans (h.across (x:=x) (y:=b) (fun e => no (e ▸ bK))).symm)

theorem Bags.prime_after_root_fold (h : Bags H G f) (r y : V) (ne : r≠y) (mate : f r=f y)
    (form : RootPairsOnly H r) : Prime G := by
  classical
  intro K hom big
  by_contra proper
  let M := pull f K
  have fat : 1<M.card := by
    obtain ⟨i,im,j,jm,ij⟩ := one_lt_card.mp big
    obtain ⟨x,rfl⟩ := h.onto i; obtain ⟨z,rfl⟩ := h.onto j
    exact one_lt_card.mpr ⟨x,mem_pull.mpr im,z,mem_pull.mpr jm,fun eq => ij (congrArg f eq)⟩
  have real : M≠univ := by
    intro top
    apply proper (eq_univ_of_forall _)
    intro i
    obtain ⟨x,rfl⟩ := h.onto i
    exact mem_pull.mp (show x∈M from top ▸ mem_univ _)
  obtain ⟨rm,sz⟩ := form M (h.modulePull K hom) fat real
  have rK := mem_pull.mp rm
  obtain ⟨j,jm,jr⟩ := exists_ne_of_one_lt_card big (f r)
  obtain ⟨z,rfl⟩ := h.onto j
  have zr : z≠r := fun eq => jr (congrArg f eq)
  have zy : z≠y := fun eq => jr ((congrArg f eq).trans mate.symm)
  have yM : y∈M := mem_pull.mpr (mate ▸ rK)
  have inc : ({z,r,y}:Finset V)⊆M := by
    intro w m
    rcases mem_insert.mp m with eq|m
    · exact eq ▸ mem_pull.mpr jm
    rcases mem_insert.mp m with eq|m
    · exact eq ▸ rm
    · exact mem_singleton.mp m ▸ yM
  have cap := card_le_card inc
  rw [card_insert_of_not_mem (by simp [zr,zy]),card_pair ne,sz] at cap
  omega

/-- The exceptional nonprime graph has an explicit two-vertex root
bag. Leaving one representative yields an induced prime quotient; the
vertices of this pair have identical adjacencies to every outside vertex. -/
theorem prime_or_root_twin (H : SimpleGraph V) (r : V) (form : RootPairsOnly H r) :
    Prime H ∨ ∃ y : V,r≠y ∧ Homogeneous H {r,y} ∧ ({r,y}:Finset V)≠univ ∧
      Prime (side H (reps {r,y} r)) := by
  classical
  by_cases prime : Prime H
  · exact Or.inl prime
  unfold Prime at prime
  push_neg at prime
  obtain ⟨M,hom,big,proper⟩ := prime
  obtain ⟨rm,sz⟩ := form M hom big proper
  obtain ⟨y,ym,yr⟩ := exists_ne_of_one_lt_card big r
  have pair : M={r,y} := (eq_of_subset_of_card_le (show ({r,y}:Finset V)⊆M from insert_subset rm (singleton_subset_iff.mpr ym)) (by rw [sz,card_pair yr.symm])).symm
  subst M
  refine Or.inr ⟨y,yr.symm,hom,proper,?_⟩
  let bags := module_bags H {r,y} hom r (mem_insert_self ..)
  exact bags.prime_after_root_fold r y yr.symm (members_same {r,y} r r y (by simp) (by simp)) form

#print axioms Bags.modulePull
#print axioms Bags.prime_after_root_fold
#print axioms prime_or_root_twin
end Minimal180.Substitution
