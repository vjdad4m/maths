import SixSevenLopsidedOre189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private lift_side_path from DegreeFiveSmallSides189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

theorem seven_lopsided_side (E : Finset V) (e7 : E.card=7) {a b : V}
    (ad : a∈E) (bd : b∈E) (ab : a≠b)
    (b2 : 2≤(inside G E b).card)
    (rest : ∀ u∈E,u≠b → 3≤(inside G E u).card)
    (profile : (∃ C : Finset V,C⊆E ∧ 4≤C.card ∧ ∀ u∈C,5≤(inside G E u).card) ∨
      (∃ C : Finset V,C⊆E ∧ C.card=6 ∧ ∀ u∈C,4≤(inside G E u).card)) :
    RouteOn G E a b := by
  classical
  let U := ↑(↑E : Set V)
  let J := G.induce (↑E : Set V)
  let a' : U := ⟨a,ad⟩
  let b' : U := ⟨b,bd⟩
  have n7 : Fintype.card U=7 := (Fintype.card_coe E).trans e7
  have hdeg (k : ℕ) (C : Finset V) (ce : C⊆E) (h : ∀ u∈C,k≤(inside G E u).card) :
      ∃ M : Finset U,M.card=C.card ∧ ∀ u∈M,k≤J.degree u := by
    let M := univ.filter (fun u : U=>u.val∈C)
    have exactC : M.card=C.card := by
      apply card_bij (fun (j : U) _=>j.val)
      · intro j m
        exact (mem_filter.mp m).2
      · intro j _ t _ e
        exact Subtype.ext e
      · intro z zm
        exact ⟨⟨z,ce zm⟩,mem_filter.mpr ⟨mem_univ _,zm⟩,rfl⟩
    refine ⟨M,exactC,fun u um=>?_⟩
    rw [←inside_card_eq_degree_induce]
    exact h _ (mem_filter.mp um).2
  have p : (∃ M : Finset U,4≤M.card ∧ ∀ u∈M,5≤J.degree u) ∨
      (∃ M : Finset U,M.card=6 ∧ ∀ u∈M,4≤J.degree u) := by
    rcases profile with ⟨C,ce,c4,h⟩|⟨C,ce,c6,h⟩
    · obtain ⟨M,mC,hm⟩ := hdeg 5 C ce h
      exact .inl ⟨M,mC.symm ▸ c4,hm⟩
    obtain ⟨M,mC,hm⟩ := hdeg 4 C ce h
    exact .inr ⟨M,mC.trans c6,hm⟩
  have ab' : a'≠b' := fun h=>ab (congrArg Subtype.val h)
  have l : 2≤J.degree b' := by rw [←inside_card_eq_degree_induce]; exact b2
  have d (u : U) (no : u≠b') : 3≤J.degree u := by
    rw [←inside_card_eq_degree_induce]
    exact rest u.val u.property (fun e=>no (Subtype.ext e))
  obtain ⟨q,qp,qs⟩ := seven_lopsided_ore (G:=J) n7 ab' l d p
  exact lift_side_path E q qp qs

#print axioms seven_lopsided_side
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
