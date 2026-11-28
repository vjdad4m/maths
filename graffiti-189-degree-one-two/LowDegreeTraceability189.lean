import LowDegreeOrders189
import EJSlackClosure189
import ArticulationGeneralClosure189

open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
namespace Graffiti189LongestPath.LowDegreeOrders
open Graffiti189LongestPath.SmallOrder

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Exact #189 at actual second degree one or two, with no order or
connectivity assumption besides connectedness. -/
theorem traceable_of_actual_low_degree (hc : G.Connected) (d : ℕ)
    (lower : 1≤d) (upper : d≤2)
    (cap : ∀ u,(EvenFrom G u).card≤d+1)
    (deg : ∀ u v : V,u≠v → d≤G.degree u ∨ d≤G.degree v)
    (attain : ∃ u : V,G.degree u≤d) : Graffiti189Ore.Traceable G := by
  classical
  obtain ⟨v,low⟩ := attain
  have h : d=1 ∨ d=2 := by omega
  rcases h with rfl|rfl
  · exact traceable_at_order_le_two_d_add_two hc 1 cap deg
      (order_le_four_of_even_two hc v low cap)
  · by_cases robust : DeletionTwoConnected G
    · exact traceable_at_order_le_two_d_add_three hc robust 2 cap deg
        (order_le_seven_of_even_three hc v low cap robust)
    · obtain ⟨S,S2,bad⟩ : ∃ S : Finset V,S.card<2 ∧ ¬(G.induce ((↑S:Set V)ᶜ)).Connected := by
        apply Classical.byContradiction
        intro no
        apply robust
        intro S small
        exact Classical.byContradiction (fun z => no ⟨S,small,z⟩)
      have one : S.card=1 := by
        by_cases zero : S.card=0
        · have empty : S=∅ := card_eq_zero.mp zero
          exfalso
          apply bad
          rw [empty,coe_empty,Set.compl_empty]
          exact (SimpleGraph.induceUnivIso G).connected_iff.mpr hc
        · omega
      obtain ⟨u,eq⟩ := card_eq_one.mp one
      have setEq : (↑S:Set V)ᶜ={z : V | z≠u} := by rw [eq]; ext z; simp
      exact Graffiti189LongestPath.CrossSaturation.traceable_at_articulation_general
        hc 2 (by decide) cap deg u (by rw [←setEq]; exact bad)

#print axioms traceable_of_actual_low_degree
end Graffiti189LongestPath.LowDegreeOrders
