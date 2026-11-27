import C7MultiRadius4Caps133

namespace Graffiti133NestedWeightedCore
open SimpleGraph Finset Graffiti133 Graffiti133NoFive Graffiti133MultiC7
open scoped Classical BigOperators
set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

noncomputable def adjTwo (H : Hole G 7) : Finset V :=
  (multiVertices H).filter (fun x => (contactSet H x).card=2 ∧
    ∃ i∈contactSet H x,∃ j∈contactSet H x,Cyclic i j)

noncomputable def scoredFar (H : Hole G 7) (u v : V) : Finset V :=
  (multiVertices H).filter (fun x => (contactSet H x).card=2 ∧
    (¬∃ i∈contactSet H x,∃ j∈contactSet H x,Cyclic i j) ∧ x≠u ∧ x≠v)

noncomputable def profileCredit (H : Hole G 7) (u v : V) (x : V) : Nat :=
  (if x∈adjTwo H then 1 else 0) + (if x∈scoredFar H u v then 2 else 0)

theorem adjacent_two_bound (H : Hole G 7) (h4 : FourCycleFree G) : (adjTwo H).card≤7 := by
  classical
  rw [←adjacent_pair_resource]
  apply Finset.card_le_card_of_injOn (contactSet H)
  · intro x xm
    obtain ⟨_,two,cyc⟩ := Finset.mem_filter.mp xm
    exact Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,two⟩,cyc⟩
  · intro x xm y ym eq
    by_contra ne
    have cap := disjoint_contact_pairs H h4 ne
    rw [eq,Finset.inter_self,(Finset.mem_filter.mp ym).2.1] at cap
    omega

theorem profile_credit_bound (H : Hole G 7) (h4 : FourCycleFree G) (u v : V)
    (h : (scoredFar H u v).card≤1) :
    (∑ x∈multiVertices H,profileCredit H u v x)≤9 := by
  classical
  unfold profileCredit
  rw [Finset.sum_add_distrib]
  have ae : (∑ x∈multiVertices H, if x∈adjTwo H then (1:Nat) else 0)=(adjTwo H).card := by
    rw [←Finset.sum_filter]
    have eq : ((multiVertices H).filter (·∈adjTwo H))=adjTwo H := by
      ext x
      exact Finset.mem_filter.trans ⟨fun p=>p.2,fun p=>⟨(Finset.mem_filter.mp p).1,p⟩⟩
    simp [eq]
  have be : (∑ x∈multiVertices H, if x∈scoredFar H u v then (2:Nat) else 0)=2*(scoredFar H u v).card := by
    rw [←Finset.sum_filter]
    have eq : ((multiVertices H).filter (·∈scoredFar H u v))=scoredFar H u v := by
      ext x
      exact Finset.mem_filter.trans ⟨fun p=>p.2,fun p=>⟨(Finset.mem_filter.mp p).1,p⟩⟩
    simp [eq,Nat.mul_comm]
  rw [ae,be]
  have r := adjacent_two_bound H h4
  omega

#print axioms profile_credit_bound
end Graffiti133NestedWeightedCore
