import EJSlackClosure189
import ThresholdFiveOrderFifteen189

namespace Graffiti189LongestPath
open Finset SimpleGraph SimpleGraph.Walk
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- At degree threshold five, every counterexample has exactly fourteen vertices. -/
theorem order_eq_fourteen_of_degree_five_counterexample
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤6)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (fail : ¬∃ a b,∃ p : G.Walk a b,p.IsPath ∧ ∀ z,z∈p.support) :
    Fintype.card V = 14 := by
  classical
  have bound := order_le_fourteen_of_degree_five_counterexample hc even degree fail
  have conn := (degree_five_counterexample_has_adjacent_cut hc even degree fail).1
  have lower : 13 < Fintype.card V := by
    apply Nat.lt_of_not_ge
    intro small
    exact fail (SmallOrder.traceable_at_order_le_two_d_add_three hc conn 5 even degree (by omega))
  omega

#print axioms order_eq_fourteen_of_degree_five_counterexample
end Graffiti189LongestPath
