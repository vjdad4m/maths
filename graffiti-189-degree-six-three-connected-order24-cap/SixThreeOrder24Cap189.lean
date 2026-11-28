import SixLayer25Model189
import SixLayer25Label189
import Equality25Impossible189
import SixOrder25BThreeExcluded189
import SixUniversalOrder25Middle189

namespace Graffiti189LongestPath
open SimpleGraph Finset

variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Order 25 does not occur in the degree-six case in connectivity at
least three. The low-degree root can have radius at most four, and its
second shell must have at least four vertices, supplying a checked
equality frame. -/
theorem order_le_twenty_four_at_degree_six_three_connected
    (hc : G.Connected)
    (cap : ∀ v, (EvenFrom G v).card ≤ 7)
    (conn : ∀ S : Finset V, S.card < 3 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ x y : V, x ≠ y → 6 ≤ G.degree x ∨ 6 ≤ G.degree y)
    (x : V) (dx : G.degree x ≤ 6) : Fintype.card V ≤ 24 := by
  classical
  have bound := order_le_twenty_five_at_degree_six hc cap x dx
  by_contra! no
  have n : Fintype.card V = 25 := by omega
  have rad := eccentricity_le_four_at_order25_degree_six hc cap conn degree (x:=x) dx n
  have b4 := four_le_second_shell_at_order25_degree_six hc cap conn degree (x:=x) dx n
  obtain ⟨e,t,b,ht,hb,M⟩ :=
    Equality25Profile.model_at_order_twenty_five_with_radius_frame hc cap degree x dx n rad
      b4 (exists_layer_twenty_five_label hc x n)
  exact Equality25Count.model_impossible ht (by omega) M

#print axioms order_le_twenty_four_at_degree_six_three_connected
end Graffiti189LongestPath
