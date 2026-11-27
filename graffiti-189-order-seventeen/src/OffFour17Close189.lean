import OffFour17Partition189
import OffFour17DiscTable189
import OffFive17Close189
import TraceableOrderSixteen189

namespace Graffiti189LongestPath.TwoCut
open Finset SimpleGraph SimpleGraph.Walk
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem no_length_twelve_with_four_omissions_at_degree_four
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card ≤ 5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4 ≤ G.degree u ∨ 4 ≤ G.degree v)
    {a b : V} {p : G.Walk a b} (hp : EdgeOptimal p) (ah : 4 ≤ G.degree a) (bh : 4 ≤ G.degree b)
    (len : p.length=12) (off : ((univ : Finset V)\p.support.toFinset).card=4) : False :=
  no_length_twelve_with_four_omissions_of_rows OffFour17.disc_row
    hc even conn degree hp ah bh len off

/-- Graffiti.pc #189 at degree threshold four on 2-connected graphs
of order at most seventeen. -/
theorem traceable_of_order_le_seventeen
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card ≤ 5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4 ≤ G.degree u ∨ 4 ≤ G.degree v)
    (order : Fintype.card V ≤ 17) :
    ∃ a b : V,∃ q : G.Walk a b,q.IsPath ∧ ∀ z,z∈q.support := by
  classical
  by_contra fail
  obtain ⟨_,a,b,p,hp,ah,bh,len,off⟩ :=
    order_seventeen_one_remaining_branch hc even conn degree
      (traceable_of_order_le_sixteen hc even conn degree) order fail
  exact no_length_twelve_with_four_omissions_at_degree_four hc even conn degree hp ah bh len off

#print axioms no_length_twelve_with_four_omissions_at_degree_four
#print axioms traceable_of_order_le_seventeen
end Graffiti189LongestPath.TwoCut
