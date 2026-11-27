import OffSix17CoreLift189
import SixCoreMarkedPath189
import OffThree17Close189

namespace Graffiti189LongestPath.TwoCut
open Finset SimpleGraph SimpleGraph.Walk
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- At degree threshold four, a ten-edge optimal path with high ends
cannot omit exactly six vertices. -/
theorem no_length_ten_with_six_omissions_at_degree_four
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    {a b : V} {p : G.Walk a b} (hp : EdgeOptimal p) (ah : 4≤G.degree a) (bh : 4≤G.degree b)
    (len : p.length=10) (off : ((univ : Finset V)\p.support.toFinset).card=6) : False :=
  no_length_ten_with_six_omissions_of_core_paths
    (by
      intro W D _ _ _ h minDeg wide s t ne
      exact Graffiti189SixCore.six_core_marked_path D h minDeg wide ne)
    (by
      intro W D _ _ _ h wide s t ne
      exact Graffiti189SixCore.five_core_marked_path D h wide ne)
    hc even conn degree hp ah bh len off

/-- Given traceability through order sixteen, a degree-four obstruction
at order seventeen can only have one of the remaining two shapes. -/
theorem order_seventeen_two_remaining_branches
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    (closed16 : Fintype.card V≤16 →
      ∃ a b : V,∃ q : G.Walk a b,q.IsPath ∧ ∀ z,z∈q.support)
    (order : Fintype.card V≤17)
    (fail : ¬∃ a b : V,∃ q : G.Walk a b,q.IsPath ∧ ∀ z,z∈q.support) :
    Fintype.card V=17 ∧
    ∃ a b : V,∃ p : G.Walk a b,EdgeOptimal p ∧ 4≤G.degree a ∧ 4≤G.degree b ∧
      ((p.length=11 ∧ ((univ : Finset V)\p.support.toFinset).card=5) ∨
       (p.length=12 ∧ ((univ : Finset V)\p.support.toFinset).card=4)) := by
  obtain ⟨ord,a,b,p,hp,ah,bh,h⟩ :=
    order_seventeen_three_remaining_branches hc even conn degree closed16 order fail
  rcases h with ⟨len,off⟩|last
  · exact (no_length_ten_with_six_omissions_at_degree_four hc even conn degree hp ah bh len off).elim
  · exact ⟨ord,a,b,p,hp,ah,bh,last⟩

#print axioms no_length_ten_with_six_omissions_at_degree_four
#print axioms order_seventeen_two_remaining_branches
end Graffiti189LongestPath.TwoCut
