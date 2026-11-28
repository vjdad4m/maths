import DegreeFiveOnlyFourteen189
import AdjacentCutFiveFourteenGlobal189

namespace Graffiti189LongestPath
open Finset SimpleGraph SimpleGraph.Walk
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Graffiti.pc #189 at degree threshold five, without any order or connectivity
restriction beyond the original hypotheses. -/
theorem traceable_at_degree_five
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤6)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v) :
    ∃ a b,∃ p : G.Walk a b,p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  apply Classical.byContradiction
  intro fail
  have low := order_le_thirteen_of_degree_five_counterexample hc even degree fail
  have high := order_eq_fourteen_of_degree_five_counterexample hc even degree fail
  omega

#print axioms traceable_at_degree_five
end Graffiti189LongestPath
