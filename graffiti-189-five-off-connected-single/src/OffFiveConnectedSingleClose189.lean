import OffFiveConnectedSingleGraph189
import OffFiveConnSingleTable189
import OffFiveConnectedTwinGraphClose189

namespace Graffiti189LongestPath.TwoCut.SmallOrderFour
open SimpleGraph SimpleGraph.Walk Finset
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

theorem traceable_if_five_off_connected_single
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    {a b : V} {p : G.Walk a b} (hp : EdgeOptimal p)
    (ah : 4≤G.degree a) (bh : 4≤G.degree b) (len : p.length=10)
    (off : ((univ : Finset V)\p.support.toFinset).card=5)
    (H : OmittedComponent p) (whole : ∀ z∉p.support,z∈H.vertices)
    (single : ∀ z∉p.support,(Pins p z).card≤1) :
    ∃ a b : V,∃ q : G.Walk a b,q.IsPath ∧ ∀ z,z∈q.support := by
  exact traceable_if_five_off_connected_single_with_table
    OffFive16ConnectedSingle.pre_of_support OffFive16ConnectedSingle.core_of_pre
    hc even conn degree hp ah bh len off H whole single

theorem traceable_if_five_off_order_sixteen
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    {a b : V} {p : G.Walk a b} (hp : EdgeOptimal p)
    (ah : 4≤G.degree a) (bh : 4≤G.degree b) (len : p.length=10)
    (off : ((univ : Finset V)\p.support.toFinset).card=5) :
    ∃ a b : V,∃ q : G.Walk a b,q.IsPath ∧ ∀ z,z∈q.support := by
  classical
  by_cases c : ∃ H : OmittedComponent p,∀ z∉p.support,z∈H.vertices
  · obtain ⟨H,whole⟩ := c
    by_cases b : ∃ x∉p.support,2≤(Pins p x).card
    · obtain ⟨x,xo,xt⟩ := b
      exact traceable_if_five_off_connected_twin hc even conn degree hp ah bh len off H (whole x xo) whole xt
    · have single : ∀ x∉p.support,(Pins p x).card≤1 := by
        intro x xo
        exact Nat.le_of_not_gt (fun xt=>b ⟨x,xo,xt⟩)
      exact traceable_if_five_off_connected_single hc even conn degree hp ah bh len off H whole single
  · exact traceable_if_five_off_disconnected hc even conn degree hp ah bh len off c

#print axioms traceable_if_five_off_connected_single
#print axioms traceable_if_five_off_order_sixteen
end Graffiti189LongestPath.TwoCut.SmallOrderFour
