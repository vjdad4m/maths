import OrderSixteenFoundation189
import FourOffComplete189
import OffFiveConnectedSingleClose189

namespace Graffiti189LongestPath.TwoCut
open SimpleGraph SimpleGraph.Walk Finset
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack

/-- Graffiti.pc #189 at degree threshold four, for 2-connected graphs
of order at most sixteen. -/
theorem traceable_of_order_le_sixteen
    {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    (order : Fintype.card V≤16) :
    ∃ a b : V,∃ q : G.Walk a b,q.IsPath ∧ ∀ z,z∈q.support := by
  classical
  by_contra absent
  obtain ⟨_,a,b,p,best,ah,bh,h⟩ :=
    OrderSixteenFoundation.order_sixteen_two_remaining_branches hc even conn degree order absent
  rcases h with ⟨len,off⟩|⟨len,off⟩
  · exact absent (SmallOrderFour.traceable_if_five_off_order_sixteen hc even conn degree best ah bh len off)
  · exact absent (SmallOrderFour.traceable_if_four_off_order_sixteen hc even conn degree best ah bh len off)

#print axioms traceable_of_order_le_sixteen
end Graffiti189LongestPath.TwoCut
