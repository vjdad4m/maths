import EightLeaves180

set_option warningAsError true
set_option compiler.extract_closed false
set_option maxHeartbeats 600000
set_option maxRecDepth 10000
namespace Minimal180.PairRepair.Eight
open Finset SimpleGraph Graffiti177 Graffiti318 Rooted180 Converse180 Assembly180 Substitution Transversals
theorem budget_value : allowance G 2 false A=2 := by
  obtain ⟨gc,par,ai,elig,_⟩ := data
  have h := allowance_eq G gc (by decide) 2 false A ai
  change 1+A.card+(parity G 2 false).card+allowance G 2 false A=
    weightedLeaves G (eligible A (parity G 2 false) 2)+Fintype.card V at h
  simp only [par,elig,leaves] at h
  have ac : A.card=3 := by decide
  have pc : P.card=5 := by decide
  have n : Fintype.card V=8 := by decide
  omega

theorem pinned_value : Protected G 2 false A := by
  obtain ⟨gc,par,ai,_,pins⟩ := data
  apply (protected_iff G gc (by decide) 2 false A ai).mpr
  refine ⟨univ\{4,7},lower_pair {4,7} (by decide),?_,?_⟩
  · simp only [par,pins]
    exact (by decide : A⊆univ\({4,7}:Finset V))
  · exact (show Fintype.card V-(univ\({4,7}:Finset V)).card≤2 by decide).trans_eq budget_value.symm

theorem unprotected_retained (Z : Finset V) (col : TwoColor G Z) (keep : A⊆Z) (size : 6≤Z.card) : (5:V)∈Z := by
  have sm := (ranks_upper Z col).2 size
  apply Classical.byContradiction
  intro absent
  have inc : (5:V)∈univ\Z := mem_sdiff.mpr ⟨mem_univ _,absent⟩
  have hit := (show ∀ s∈pairs,(5:V)∈s → (0:V)∈s by decide) _ sm inc
  exact (mem_sdiff.mp hit).2 (keep (by decide : (0:V)∈A))

theorem ordinary_value : 1+independence G+maxEven G≤maxLeaves G+bipartiteNum G := by
  have rank : Fintype.card V≤bipartiteNum G+2 := by
    simp only [exact_pairs.1]
    exact (by decide : Fintype.card V≤6+2)
  exact ordinary_of_rooted G data.1 (RootEar.family_of_rank G data.1 (by decide) rank).rooted

theorem obstruction : Prime G ∧ G.Connected ∧ (∀ y,¬DomEdge G 2 y) ∧
    ¬G.Adj 0 5 ∧ G.degree 0=4 ∧ Indep G A ∧ allowance G 2 false A=2 ∧
    TwoColor G (univ\X) ∧ Protected G 2 false A ∧
    (∀ Z,TwoColor G Z → A⊆Z → 6≤Z.card → 5∈Z) ∧
    1+independence G+maxEven G≤maxLeaves G+bipartiteNum G := by
  have deg : G.degree 0=4 := by
    exact (card_neighborFinset_eq_degree G 0).symm.trans (by decide : (G.neighborFinset 0).card=4)
  exact ⟨prime,data.1,by unfold DomEdge;decide,by decide,deg,data.2.2.1,budget_value,
    lower_pair X (by decide),pinned_value,unprotected_retained,ordinary_value⟩

#print axioms budget_value
#print axioms pinned_value
#print axioms unprotected_retained
#print axioms Eight.obstruction
end Minimal180.PairRepair.Eight
