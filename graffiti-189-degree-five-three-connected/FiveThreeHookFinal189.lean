import FiveThreeHookDispatch189
import StandaloneShellQuadratic189

namespace Graffiti189LongestPath.FiveThreeHook
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

/-- Graffiti.pc #189 at degree threshold five when deletion of any
two or fewer vertices leaves the graph connected. -/
theorem traceable_degree_five_three_connected
    (hc : G.Connected) (cap : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<3 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v) :
    ∃ a b,∃ p : G.Walk a b,p.IsPath ∧ ∀ z,z∈p.support := by
  apply traceable_degree_five_three_connected_of_shell_three hc cap conn degree
  intro x
  have f := StandaloneShellQuadratic.universal_shell_three_quadratic hc 5
    (fun v=>distanceTwo_le_of_even 5 v (cap v)) x
  omega

#print axioms traceable_degree_five_three_connected
end Graffiti189LongestPath.FiveThreeHook
