import FourOffTwinGraph189
import FourOffSoloGraph189

namespace Graffiti189LongestPath.TwoCut.SmallOrderFour
open SimpleGraph SimpleGraph.Walk Finset
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
variable {V : Type*} {G : SimpleGraph V}
set_option maxHeartbeats 2200000
set_option linter.unusedSectionVars false
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V} {p : G.Walk a b} {x : V}
open private no_endpoints dist_two pin_data pin_of_neighbor_mem pin_pos mem_distanceTwo card_pinVertices cardinal_flankVertices LeftMarks RightMarks card_leftMarks card_rightMarks same_support_optimal reverse_long reverse_pin mark_length degree_off_bound two_flanks_full second_pin_no_start_of_high from SmallOrderFour189
open private left_boundary_porters_at_most_two length_eleven_four_off_single_pin_shape length_eleven_four_off_two_pin_shape from FourOffGraphCore189
open private length_eleven_four_off_two_pin_mixed_spans from FourOffTwinMixed189
open private length_eleven_four_off_two_boundary_pins_span from FourOffTwinBoundary189

theorem traceable_if_four_off_order_sixteen_some_two_pin
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    {a b z : V} {p : G.Walk a b} (hp : EdgeOptimal p)
    (ah : 4≤G.degree a) (bh : 4≤G.degree b) (len : p.length=11)
    (off : ((univ : Finset V)\p.support.toFinset).card=4)
    (zo : z∉p.support) (two : 2≤(Pins p z).card) :
    ∃ a b : V, ∃ q : G.Walk a b,q.IsPath ∧ ∀ v,v∈q.support := by
  exact traceable_if_four_off_order_sixteen_some_two_pin_with_table OffFour16Twin.all_rows
    (length_eleven_four_off_two_pin_mixed_spans left_boundary_porters_at_most_two)
    length_eleven_four_off_two_boundary_pins_span length_eleven_four_off_two_pin_shape hc even conn degree hp ah bh len off zo two
#print axioms traceable_if_four_off_order_sixteen_some_two_pin

theorem traceable_if_four_off_order_sixteen
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    {a b : V} {p : G.Walk a b} (hp : EdgeOptimal p)
    (ah : 4≤G.degree a) (bh : 4≤G.degree b) (len : p.length=11)
    (off : ((univ : Finset V)\p.support.toFinset).card=4) :
    ∃ a b : V, ∃ q : G.Walk a b,q.IsPath ∧ ∀ v,v∈q.support := by
  classical
  by_cases few : ∀ z∉p.support,(Pins p z).card≤1
  · exact traceable_if_four_off_order_sixteen_all_single_pins_with_table
      OffFour16Solo.all_rows length_eleven_four_off_single_pin_shape
      hc even conn degree hp ah bh len off few
  · push_neg at few
    obtain ⟨z,zo,two⟩ := few
    exact traceable_if_four_off_order_sixteen_some_two_pin hc even conn degree hp ah bh len off zo (by omega)
#print axioms traceable_if_four_off_order_sixteen
end Graffiti189LongestPath.TwoCut.SmallOrderFour
