import OffFive17Close189
import TraceableOrderSixteen189

namespace Graffiti189LongestPath.TwoCut
open Finset SimpleGraph SimpleGraph.Walk
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack

/-- An order-at-most-17 counterexample in the degree-four 2-connected case
has order exactly 17 and the indicated path shape. -/
theorem degree_four_order17_counterexample_one_branch
    {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    (order : Fintype.card V≤17)
    (fail : ¬∃ a b : V,∃ q : G.Walk a b,q.IsPath ∧ ∀ z,z∈q.support) :
    Fintype.card V=17 ∧
    ∃ a b : V,∃ p : G.Walk a b,EdgeOptimal p ∧ 4≤G.degree a ∧ 4≤G.degree b ∧
      p.length=12 ∧ ((univ : Finset V)\p.support.toFinset).card=4 :=
  order_seventeen_one_remaining_branch hc even conn degree
    (traceable_of_order_le_sixteen hc even conn degree) order fail

#print axioms degree_four_order17_counterexample_one_branch
end Graffiti189LongestPath.TwoCut
