import OffFive17MarkedGraph189
import OffFive17MarkedTable189
import OffFive17SingletonGraph189
import OffFive17SingletonTable189
import OffSix17Close189

namespace Graffiti189LongestPath.TwoCut
open Finset SimpleGraph SimpleGraph.Walk
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem no_length_eleven_with_five_omissions_at_degree_four
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card ≤ 5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4 ≤ G.degree u ∨ 4 ≤ G.degree v)
    {a b : V} {p : G.Walk a b} (hp : EdgeOptimal p) (ah : 4 ≤ G.degree a) (bh : 4 ≤ G.degree b)
    (len : p.length=11) (off : ((univ : Finset V)\p.support.toFinset).card=5) : False := by
  classical
  obtain ⟨H,lo,hi,one,pins,left,right⟩ :=
    length_eleven_five_off_has_central_component hc even conn degree hp ah bh len off
  by_cases c : H.vertices.card=4
  · exact no_length_eleven_with_central_four_component_of_endpoint_table OffFive17Singleton.all_rows
      hc even conn degree hp ah bh len off H c one left right
  refine no_length_eleven_with_central_five_component_of_marked_core ?_
    hc even conn degree hp ah bh len H (by omega) one pins left right
  intro W D _ _ _ m h l r min wide leaf
  exact OffFive17MarkedCore.marked_core_of_table D OffFive17MarkedCore.all_rows m h l r min wide leaf

theorem order_seventeen_one_remaining_branch
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card ≤ 5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4 ≤ G.degree u ∨ 4 ≤ G.degree v)
    (closed16 : Fintype.card V ≤ 16 →
      ∃ a b : V,∃ q : G.Walk a b,q.IsPath ∧ ∀ z,z∈q.support)
    (order : Fintype.card V ≤ 17)
    (fail : ¬∃ a b : V,∃ q : G.Walk a b,q.IsPath ∧ ∀ z,z∈q.support) :
    Fintype.card V=17 ∧
    ∃ a b : V,∃ p : G.Walk a b,EdgeOptimal p ∧ 4 ≤ G.degree a ∧ 4 ≤ G.degree b ∧
      p.length=12 ∧ ((univ : Finset V)\p.support.toFinset).card=4 := by
  obtain ⟨ord,a,b,p,hp,ah,bh,h⟩ :=
    order_seventeen_two_remaining_branches hc even conn degree closed16 order fail
  rcases h with ⟨len,off⟩|last
  · exact (no_length_eleven_with_five_omissions_at_degree_four hc even conn degree hp ah bh len off).elim
  · exact ⟨ord,a,b,p,hp,ah,bh,last⟩

#print axioms no_length_eleven_with_five_omissions_at_degree_four
#print axioms order_seventeen_one_remaining_branch
end Graffiti189LongestPath.TwoCut
