import SixSingletonQ2Actual189
import SixSingletonFiveVisibleComplete189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph Finset ArticulationPair Graffiti189Ore
open private Shore from AdjacentCutFiveActual189
open private Cmp DeletionConnected from SixCutFar189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

/-- At degree six, every order-sixteen adjacent two-cut with one singleton component is traceable. -/
theorem traceable_of_adjacent_singleton_thirteen
    (hc : G.Connected) (ab : G.Adj a b) (even : ∀ z,(EvenFrom G z).card≤7)
    (conn : DeletionConnected G) (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {S D : Cmp G a b} (sd : S≠D)
    (cover : ∀ {z : V},z≠a → z≠b → z∈Shore S ∨ z∈Shore D)
    (one : (Shore S).card=1) (d13 : (Shore D).card=13) : Traceable G := by
  rcases adjacent_singleton_thirteen_visible_profile hc ab even conn degree sd cover one d13 with h|h
  · exact traceable_of_adjacent_singleton_thirteen_five_visible hc ab even conn degree sd cover one d13 h.1
  exact traceable_of_adjacent_singleton_thirteen_six_visible hc ab even conn degree sd cover one d13 h.1

#print axioms traceable_of_adjacent_singleton_thirteen
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
