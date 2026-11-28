import SixLayer25Model189
import SixLayer25Label189
import Equality25Impossible189
import SixFourOrderTwentyFour189

namespace Graffiti189LongestPath
open SimpleGraph Finset

variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Graffiti.pc #189 for actual second-smallest degree six and connectivity
at least four, with no restriction on graph order. -/
theorem traceable_at_degree_six_four_connected
    (hc : G.Connected)
    (cap : ∀ v, (EvenFrom G v).card ≤ 7)
    (conn : ∀ S : Finset V, S.card < 4 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ x y : V, x ≠ y → 6 ≤ G.degree x ∨ 6 ≤ G.degree y)
    (attained : ∃ x : V, G.degree x ≤ 6) :
    Graffiti189Ore.Traceable G := by
  classical
  obtain ⟨x,dx⟩ := attained
  have overall := order_le_twenty_five_at_degree_six_four_connected hc cap conn x dx
  by_cases small : Fintype.card V ≤ 24
  · exact SixFourOrderTwentyFour.traceable_order_twenty_four hc cap conn degree small
  have equality : Fintype.card V=25 := by omega
  obtain ⟨e,t,b,ht,hb,M⟩ := Equality25Profile.model_at_order_twenty_five_of_label hc cap conn degree x dx equality
    (exists_layer_twenty_five_label hc x equality)
  exact (Equality25Count.model_impossible ht (by omega) M).elim

#print axioms traceable_at_degree_six_four_connected
end Graffiti189LongestPath
