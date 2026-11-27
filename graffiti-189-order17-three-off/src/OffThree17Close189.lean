import OffThree17Graph189
import OffThree17LongerTable189
import OrderSeventeenFoundationLink189

namespace Graffiti189LongestPath.TwoCut
open Finset SimpleGraph SimpleGraph.Walk
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack

variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem no_length_thirteen_with_three_off_at_degree_four
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    {a b : V} {p : G.Walk a b} (hp : EdgeOptimal p) (ah : 4≤G.degree a) (bh : 4≤G.degree b)
    (len : p.length=13) (off : ((univ : Finset V)\p.support.toFinset).card=3) : False :=
  no_length_thirteen_with_three_off_at_degree_four_table OffThree17Longer.all_rows
    hc even conn degree hp ah bh len off

theorem order_seventeen_three_remaining_branches
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
       (p.length=12 ∧ ((univ : Finset V)\p.support.toFinset).card=4)) := by
  obtain ⟨ord,a,b,p,hp,ah,bh,h⟩ :=
    order_seventeen_four_remaining_branches hc even conn degree closed16 order fail
  rcases h with h|h|h|⟨len,off⟩
  · exact ⟨ord,a,b,p,hp,ah,bh,.inl h⟩
  · exact ⟨ord,a,b,p,hp,ah,bh,.inr (.inl h)⟩
  · exact ⟨ord,a,b,p,hp,ah,bh,.inr (.inr h)⟩
  · exact (no_length_thirteen_with_three_off_at_degree_four hc even conn degree hp ah bh len off).elim

#print axioms no_length_thirteen_with_three_off_at_degree_four
#print axioms order_seventeen_three_remaining_branches
end Graffiti189LongestPath.TwoCut
