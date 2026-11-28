import SixThree20SingletonClose189
import SixThree20Frontier189
import SixThree20NoHigh189

namespace Graffiti189LongestPath.SixThreeTwenty
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
open Graffiti189LongestPath.SixThreeSixteen (ConnThree length_ge_twelve)
open Graffiti189LongestPath.SixThreeEighteen (Omit mem_Omit omit_add_length not_length_twelve_of_three_active)
open private Graffiti189LongestPath.boundary_card_of_connectivity from SmallSeparator189
open private Graffiti189LongestPath.OneSlack.pin_of_neighbor_mem from OneSlack189
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem longest_nonspanning_length_thirteen_or_fourteen (hc : G.Connected) (conn : ConnThree G)
    (cap : ∀ v,(EvenFrom G v).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (ord : Fintype.card V=20) {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    {x : V} (hx : x∉p.support) : p.length=13 ∨ p.length=14 := by
  rcases longest_shape_at_twenty hc conn cap degree ord hp hx with a | b | ⟨_, c, _⟩
  · exact Or.inl a
  · exact Or.inr b
  · exact (no_nonspanning_length_eighteen_at_twenty hc conn cap degree (by omega) hp c hx).elim
#print axioms longest_nonspanning_length_thirteen_or_fourteen
end Graffiti189LongestPath.SixThreeTwenty
