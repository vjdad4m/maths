import FiveThreeHookFinal189
import ArticulationGeneralClosure189
import DegreeFiveNonadjacentComplete189

namespace Graffiti189LongestPath
open Finset SimpleGraph SimpleGraph.Walk
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- At threshold five, every counterexample is 2-connected and has an adjacent
two-vertex separator. The input degree condition allows one low vertex. -/
theorem degree_five_counterexample_has_adjacent_cut
    (hc : G.Connected) (even : ∀ x,(EvenFrom G x).card≤6)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (fail : ¬∃ a b,∃ p : G.Walk a b,p.IsPath ∧ ∀ z,z∈p.support) :
    (∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected) ∧
    ∃ a b : V,G.Adj a b ∧ ¬(G.induce {z : V | z≠a ∧ z≠b}).Connected := by
  classical
  have empty_eq : (↑(∅ : Finset V) : Set V)ᶜ = Set.univ := by simp
  have empty_conn : (G.induce ((↑(∅ : Finset V) : Set V)ᶜ)).Connected := by
    rw [empty_eq]
    exact (SimpleGraph.induceUnivIso G).connected_iff.mpr hc
  have conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected := by
    intro R r
    by_cases r0 : R.card=0
    · rw [Finset.card_eq_zero.mp r0]; exact empty_conn
    have ⟨c,rc⟩ := Finset.card_eq_one.mp (show R.card=1 by omega)
    subst R
    apply Classical.byContradiction; intro deletionFails
    have eq : (↑({c} : Finset V) : Set V)ᶜ = {z : V | z≠c} := by ext z; simp
    rw [eq] at deletionFails
    exact fail (CrossSaturation.traceable_at_articulation_general hc 5 (by decide)
      even degree c deletionFails)
  refine ⟨conn,?_⟩
  have bad3 : ¬∀ R : Finset V,R.card<3 → (G.induce ((↑R : Set V)ᶜ)).Connected :=
    fun h => fail (FiveThreeHook.traceable_degree_five_three_connected hc even h degree)
  push_neg at bad3
  obtain ⟨R,small,cut⟩ := bad3
  have large : 2≤R.card := Nat.le_of_not_gt (fun h=>cut (conn R h))
  obtain ⟨a,b,ne,rr⟩ := Finset.card_eq_two.mp (show R.card=2 by omega)
  have eq : (↑R : Set V)ᶜ = {z : V | z≠a ∧ z≠b} := by
    ext z
    simp [rr,not_or]
  rw [eq] at cut
  refine ⟨a,b,?_,cut⟩
  apply Classical.byContradiction; intro missingEdge
  exact fail (CrossSaturation.FiveActualCut.traceable_at_actual_five_nonadjacent_cut
    hc ne missingEdge even conn degree cut)

#print axioms degree_five_counterexample_has_adjacent_cut
end Graffiti189LongestPath
