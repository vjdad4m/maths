import SixThree20SingletonClose189
import SixThree20FourteenClose189

namespace Graffiti189LongestPath.SixThreeTwenty
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
open Graffiti189LongestPath.SixThreeSixteen (ConnThree)
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem traceable_six_at_three_connectivity_order_twenty
    (hc : G.Connected) (conn : ConnThree G) (cap : ∀ v,(EvenFrom G v).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (ord : Fintype.card V≤20) :
    ∃ (a b : V) (p : G.Walk a b),p.IsPath ∧ ∀ v,v∈p.support := by
  classical
  by_cases small : Fintype.card V≤19
  · exact Graffiti189LongestPath.SixThreeNineteen.traceable_six_at_three_connectivity_order_nineteen
      hc conn cap degree small
  have exactOrder : Fintype.card V=20 := by omega
  obtain ⟨a,b,p,hp⟩ := Graffiti189LongestPath.Rigidity.exists_longest hc
  by_cases out : ∃ x,x∉p.support
  swap
  · exact ⟨a,b,p,hp.1,fun x => Classical.byContradiction (fun h => out ⟨x,h⟩)⟩
  obtain ⟨x,hx⟩ := out
  exfalso
  rcases longest_shape_at_twenty hc conn cap degree exactOrder hp hx with n13|n14|⟨_,n18,_⟩
  · exact no_nonspanning_length_thirteen_at_twenty hc conn cap degree exactOrder hp n13 hx
  · exact no_nonspanning_length_fourteen_at_twenty hc conn cap degree exactOrder hp n14 hx
  exact no_nonspanning_length_eighteen_at_twenty hc conn cap degree ord hp n18 hx

#print axioms traceable_six_at_three_connectivity_order_twenty
end Graffiti189LongestPath.SixThreeTwenty
