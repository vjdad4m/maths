import DegreeFiveNearSixTerm189
import WingSignature189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset
open private Shore shore_off shore_closed shore_disjoint from DegreeFiveActualCut189
open private Cmp from DegreeFiveThreeForeignImpossible189
open private inside_high_at_least_four_if_exclusive inside_high_at_least_three from DegreeFiveBalancedCommonRoot189
open private anywhere_high_of_two from DegreeFiveDistanceTwoThreeClose189
open private nonport_neighbors_subset nonport_degree_bound_small from DegreeFiveThreeFiveShapes189
open ArticulationPair
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

theorem terminal_route_on_four_vertices_with_two_ports
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C : Cmp (G:=G) (a:=a) (b:=b)}
    (C2 : 2≤(cutPorts C).card) (s4 : (Shore C).card=4)
    {x : V} (xc : x∈Shore C) (ax : G.Adj a x) (bx : G.Adj b x) :
    WingRealizes G a b (Shore C) .terminal := by
  classical
  let S := Shore C
  have xP : x∈cutPorts C := mem_filter.mpr ⟨xc,.inl ax⟩
  have other : ∃ t∈cutPorts C,t≠x := by
    apply Classical.byContradiction
    intro no
    have sub : cutPorts C⊆{x} := fun t tp=>mem_singleton.mpr
      (Classical.byContradiction (fun h=>no ⟨t,tp,h⟩))
    have h := card_le_card sub
    rw [card_singleton] at h
    omega
  obtain ⟨t,tp,tx⟩ := other
  obtain ⟨ts,tHit⟩ := mem_filter.mp tp
  have route : RouteOn G S x t := by
    have cap : S.card=4 := s4
    have univ (v : V) (vs : v∈S) (vh : 5≤G.degree v) :
        ∀ w∈S,v≠w → G.Adj v w := by
      have sub : inside G S v⊆S.erase v := by
        intro q h
        obtain ⟨qs,e⟩ := mem_filter.mp h
        exact mem_erase.mpr ⟨e.ne.symm,qs⟩
      have lower : 3≤(inside G S v).card := inside_high_at_least_three vs vh
      have eq : inside G S v=S.erase v := eq_of_subset_of_card_le sub (by
        rw [card_erase_of_mem vs]
        omega)
      intro w ws vw
      have t : w∈inside G S v := by rw [eq]; exact mem_erase.mpr ⟨vw.symm,ws⟩
      exact (mem_filter.mp t).2
    have cl : CompleteOn G S := by
      intro v vs w ws vw
      rcases degree v w vw with v5|w5
      · exact univ v vs v5 w ws vw
      exact (univ w ws w5 v vs vw.symm).symm
    obtain ⟨q,qp,qs⟩ := path_between_in_clique S cl xc ts tx.symm
    exact ⟨q,qp,qs⟩
  rcases tHit with at'|bt
  · exact ⟨t,x,at',bx,route.reverse⟩
  exact ⟨x,t,ax,bt,route⟩

#print axioms terminal_route_on_four_vertices_with_two_ports
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
