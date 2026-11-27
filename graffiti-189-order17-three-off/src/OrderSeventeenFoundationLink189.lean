import OrderSeventeenStructural189
import OrderSixteenFoundation189

namespace Graffiti189LongestPath.TwoCut
open SimpleGraph SimpleGraph.Walk Finset
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
open private length_eight_pins omitted_distance_two_or_all_adj
  saturated_single_port_position five_off_force_chord from OrderSixteenFoundation189

variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- High-ended edge-optimal paths with an omission cannot have length eight,
regardless of the order of the graph or number of omitted components. -/
theorem no_length_eight_with_omission_at_degree_four
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    {a b z : V} {p : G.Walk a b} (hp : EdgeOptimal p)
    (ah : 4≤G.degree a) (bh : 4≤G.degree b) (len : p.length=8)
    (off : z∉p.support) : False := by
  classical
  obtain ⟨S,_,sne,soff,sclosed,sjoined⟩ := exists_omitted_component off
  let H : OmittedComponent p := ⟨S,sne,soff,sclosed,sjoined⟩
  obtain ⟨few,ends⟩ := length_eight_pins hc even conn degree hp ah bh len
  refine no_longest_eight_from_saturated_port_rules hc even conn degree hp ah bh len H few ?_ ?_
  · intro x y xH yH xy i j hi hj gap
    exact saturated_single_port_position hc even hp.1 len few ends (H.off _ xH) (H.off _ yH)
      hi hj gap (omitted_distance_two_or_all_adj hc H xH yH xy)
  · intro x y xH yH xy hi hj
    exact five_off_force_chord hc even hp.1 len ends (H.off _ xH) (H.off _ yH) xy
      hi hj (.inl rfl) (.inr rfl) (by decide)

theorem order_seventeen_four_remaining_branches
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    (closed16 : Fintype.card V≤16 →
      ∃ a b : V,∃ q : G.Walk a b,q.IsPath ∧ ∀ z,z∈q.support)
    (order : Fintype.card V≤17)
    (fail : ¬∃ a b : V,∃ q : G.Walk a b,q.IsPath ∧ ∀ z,z∈q.support) :
    Fintype.card V=17 ∧
    ∃ a b : V,∃ p : G.Walk a b,EdgeOptimal p ∧ 4≤G.degree a ∧ 4≤G.degree b ∧
      ((p.length=10 ∧ ((univ : Finset V)\p.support.toFinset).card=6) ∨
       (p.length=11 ∧ ((univ : Finset V)\p.support.toFinset).card=5) ∨
       (p.length=12 ∧ ((univ : Finset V)\p.support.toFinset).card=4) ∨
       (p.length=13 ∧ ((univ : Finset V)\p.support.toFinset).card=3)) := by
  classical
  obtain ⟨ord,a,b,p,hp,ah,bh,sh⟩ := order_seventeen_shape_from_short_reductions hc even conn degree closed16
    (OrderSixteenFoundation.order_le_thirteen_of_unique_omission_at_degree_four hc even conn degree)
    (OrderSixteenFoundation.no_length_nine_with_two_to_seven_omissions hc even conn degree)
    order fail
  rcases sh with ⟨len,_⟩|h
  · obtain ⟨z,zo⟩ : ∃ u,u∉p.support := not_forall.mp (fun hall => fail ⟨a,b,p,hp.1.1,hall⟩)
    exact (no_length_eight_with_omission_at_degree_four hc even conn degree hp ah bh len zo).elim
  · exact ⟨ord,a,b,p,hp,ah,bh,h⟩

#print axioms no_length_eight_with_omission_at_degree_four
#print axioms order_seventeen_four_remaining_branches
end Graffiti189LongestPath.TwoCut
