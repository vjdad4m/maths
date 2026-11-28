import Equality24Complete189

namespace Graffiti189LongestPath.Equality24Profile
open SimpleGraph Finset

/-- Pairwise high degree and two vertices of degree at most six express exact
second-smallest degree six, without requiring a sorted vertex enumeration. -/
theorem impossible_order_twenty_four_at_exact_second_smallest_six
    {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hc : G.Connected)
    (cap : ∀ v,(EvenFrom G v).card≤7)
    (conn : ∀ S : Finset V,S.card<3→(G.induce ((↑S:Set V)ᶜ)).Connected)
    (minimum : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (maximum : ∃ u v : V,u≠v ∧ G.degree u≤6 ∧ G.degree v≤6)
    (n : Fintype.card V=24) : False := by
  obtain ⟨u,v,ne,du,dv⟩ := maximum
  rcases minimum u v ne with h|h
  · exact impossible_order_twenty_four_at_degree_six_three_connected hc cap conn minimum u (le_antisymm du h) n
  · exact impossible_order_twenty_four_at_degree_six_three_connected hc cap conn minimum v (le_antisymm dv h) n

theorem order_le_twenty_three_of_exact_second_smallest_six_of_order_le_twenty_four
    {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hc : G.Connected)
    (cap : ∀ v,(EvenFrom G v).card≤7)
    (conn : ∀ S : Finset V,S.card<3→(G.induce ((↑S:Set V)ᶜ)).Connected)
    (minimum : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (maximum : ∃ u v : V,u≠v ∧ G.degree u≤6 ∧ G.degree v≤6)
    (bound : Fintype.card V≤24) : Fintype.card V≤23 := by
  by_contra! bad
  exact impossible_order_twenty_four_at_exact_second_smallest_six hc cap conn minimum maximum (by omega)

#print axioms impossible_order_twenty_four_at_exact_second_smallest_six
#print axioms order_le_twenty_three_of_exact_second_smallest_six_of_order_le_twenty_four
end Graffiti189LongestPath.Equality24Profile
