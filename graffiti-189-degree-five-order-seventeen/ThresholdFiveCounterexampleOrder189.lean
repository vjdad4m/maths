import DegreeFiveReduction189
import AdjacentCutFiveTopFlatten189
import AdjacentCutFiveThreeExactViaCombinator189

namespace Graffiti189LongestPath
open Finset SimpleGraph SimpleGraph.Walk
open CrossSaturation.FiveAdjacent
open private CutGraph from AdjacentCutFiveActual189
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

/-- A connected threshold-five counterexample has at most seventeen vertices. -/
theorem order_le_seventeen_of_degree_five_counterexample
    (hc : G.Connected) (even : ∀ x,(EvenFrom G x).card≤6)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (fail : ¬∃ a b,∃ p : G.Walk a b,p.IsPath ∧ ∀ z,z∈p.support) :
    Fintype.card V≤17 := by
  classical
  by_contra large
  obtain ⟨conn,a,b,ab,cut⟩ := degree_five_counterexample_has_adjacent_cut hc even degree fail
  let J := CutGraph (G:=G) a b
  have notSub : ¬ ((univ : Finset V) ⊆ ({a,b} : Finset V)) := by
    intro sub
    have c := card_le_card sub
    rw [card_univ,card_insert_of_not_mem (by simpa using ab.ne),card_singleton] at c
    omega
  obtain ⟨z,_,zab⟩ := not_subset.mp notSub
  have nz : z≠a ∧ z≠b := by simpa [not_or] using zab
  letI : Nonempty {z : V | z≠a ∧ z≠b} := ⟨⟨z,nz⟩⟩
  have h : 2≤Nat.card J.ConnectedComponent := by
    by_contra few
    have ss : Subsingleton J.ConnectedComponent := by
      by_contra no
      have nt := not_subsingleton_iff_nontrivial.mp no
      apply few
      haveI : Finite J.ConnectedComponent := Finite.of_surjective J.connectedComponentMk (fun c=>c.exists_rep)
      letI : Fintype J.ConnectedComponent := Fintype.ofFinite _
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card_iff_nontrivial.mpr nt
    apply cut
    constructor
    intro u v
    exact ConnectedComponent.exact (ss.allEq (J.connectedComponentMk u) (J.connectedComponentMk v))
  have two := component_card_eq_two_at_genuine_adjacent_cut hc ab even conn degree h
  exact large (order_le_seventeen_of_actual_adjacent_two_shores hc ab even conn degree two)

theorem traceable_at_degree_five_of_order_eighteen
    (hc : G.Connected) (even : ∀ x,(EvenFrom G x).card≤6)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (big : 18≤Fintype.card V) :
    ∃ a b,∃ p : G.Walk a b,p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  by_contra no
  have small := order_le_seventeen_of_degree_five_counterexample hc even degree no
  omega

#print axioms order_le_seventeen_of_degree_five_counterexample
#print axioms traceable_at_degree_five_of_order_eighteen
end Graffiti189LongestPath
