import DegreeFiveComplete189
import DegreeFour189
import DegreeThreeComplete189
import LowDegreeTraceability189

namespace Graffiti189LongestPath
open Finset SimpleGraph SimpleGraph.Walk
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Graffiti.pc #189 for actual second-smallest degree from one through five.
The two degree assumptions express that all but at most one vertex have
degree at least d, and that d is attained or undercut by some vertex. -/
theorem traceable_at_actual_degree_at_most_five (hc : G.Connected) (d : ℕ)
    (low : 1 ≤ d) (high : d ≤ 5)
    (even : ∀ v,(EvenFrom G v).card ≤ d+1)
    (degree : ∀ u v : V,u≠v → d≤G.degree u ∨ d≤G.degree v)
    (attain : ∃ u : V,G.degree u ≤ d) : Graffiti189Ore.Traceable G := by
  by_cases tiny : d ≤ 2
  · exact LowDegreeOrders.traceable_of_actual_low_degree hc d low tiny even degree attain
  have one : d = 3 ∨ d = 4 ∨ d = 5 := by omega
  rcases one with rfl | rfl | rfl
  · exact GraphSat.traceable_at_actual_degree_three hc even degree attain
  · exact CrossSaturation.traceable_degree_four hc even degree
  · exact traceable_at_degree_five hc even degree

#print axioms traceable_at_actual_degree_at_most_five
end Graffiti189LongestPath
