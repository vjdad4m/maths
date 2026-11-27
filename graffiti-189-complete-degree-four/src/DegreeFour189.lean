import ArticulationClosure189
import DegreeFourTwoConnected189
import OreClosure189

universe w
namespace Graffiti189LongestPath.CrossSaturation
open SimpleGraph SimpleGraph.Walk Finset
variable {V : Type w} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

private theorem empty_deletion_connected (hc : G.Connected) :
    (G.induce ((↑(∅ : Finset V) : Set V)ᶜ)).Connected := by
  obtain ⟨x⟩ := hc.nonempty
  have h : (G.induce (↑(univ : Finset V) : Set V)).Connected := by
    apply induced_connected_of_joined _ ⟨x,mem_univ x⟩
    intro u _ v _
    obtain ⟨q⟩ := hc.preconnected u v
    exact ⟨q,fun z _=>mem_univ z⟩
  have e : ((↑(∅ : Finset V) : Set V)ᶜ) = ↑(univ : Finset V) := by
    ext z
    simp only [Set.mem_compl_iff,Finset.mem_coe,Finset.not_mem_empty,Finset.mem_univ,not_false_eq_true]
  rw [e]
  exact h

/-- Graffiti.pc #189 at degree threshold four, with no restriction on
the order or vertex connectivity of the graph. -/
theorem traceable_degree_four (hc : G.Connected)
    (even : ∀ x, (EvenFrom G x).card≤5)
    (degree : ∀ x y : V,x≠y → 4≤G.degree x ∨ 4≤G.degree y) :
    ∃ a b : V,∃ p : G.Walk a b,p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  let ore : RootedClosureAPI.{w} := by
    intro U _ _ J K _ _ sub root hdeg hp
    exact Graffiti189Ore.rooted_closure sub root hdeg hp
  by_cases conn : ∀ C : Finset V,C.card<2 → (G.induce ((↑C : Set V)ᶜ)).Connected
  · exact traceable_degree_four_two_connected hc even conn degree
  push_neg at conn
  obtain ⟨C,csmall,cut⟩ := conn
  have cOne : C.card=1 := by
    by_cases zero : C.card=0
    · have e := card_eq_zero.mp zero
      subst C
      exact (cut (empty_deletion_connected hc)).elim
    omega
  obtain ⟨c,rfl⟩ := card_eq_one.mp cOne
  have s : ((↑({c} : Finset V) : Set V)ᶜ) = {x : V | x≠c} := by
    ext z
    simp only [Set.mem_compl_iff,Finset.mem_coe,Finset.mem_singleton,Set.mem_setOf_eq]
  have cut' : ¬(G.induce {x : V | x≠c}).Connected := s ▸ cut
  exact traceable_at_articulation_of_rooted_closure ore hc even degree c cut'

#print axioms traceable_degree_four
end Graffiti189LongestPath.CrossSaturation
