import DegreeFiveBothFiveSmallRoot189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph Finset ArticulationPair
open private Shore from DegreeFiveActualCut189
open private Cmp from DegreeFiveThreeForeignImpossible189
open private sharedPortSet inside_high_at_least_four_if_exclusive from DegreeFiveBalancedCommonRoot189
open private cut_mem_iff from DegreeFiveBothFiveResidual189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

/-- A saturated five-vertex all-port shore with universal common
vertices is a clique, even with one possible low vertex. -/
theorem terminal_route_at_five_vertex_all_port_shore
    (degree : ∀ u v : V,u≠v → 5 ≤ G.degree u ∨ 5 ≤ G.degree v)
    {C : Cmp (G:=G) (a:=a) (b:=b)}
    (five : (cutPorts C).card=5) (size : (Shore C).card=5)
    {x : V} (xk : x∈sharedPortSet C)
    (univ : ∀ u∈sharedPortSet C,∀ w∈Shore C,u≠w → G.Adj u w) :
    ∃ u v : V,G.Adj a u ∧ G.Adj b v ∧ RouteOn G (Shore C) u v := by
  classical
  let S := Shore C
  have eq : cutPorts C=S := eq_of_subset_of_card_le (filter_subset _ _) (by
    rw [five]; exact size.le)
  have hi (u : V) (us : u∈S) (u5 : 5 ≤ G.degree u) (v : V) (vs : v∈S) (uv : u≠v) :
      G.Adj u v := by
    by_cases k : G.Adj a u ∧ G.Adj b u
    · exact univ u (mem_filter.mpr ⟨us,k⟩) v vs uv
    have p : 4≤(inside G S u).card := inside_high_at_least_four_if_exclusive us u5 k
    have sub : inside G S u⊆S.erase u := by
      intro w wm
      obtain ⟨ws,uw⟩ := mem_filter.mp wm
      exact mem_erase.mpr ⟨uw.ne.symm,ws⟩
    have e := eq_of_subset_of_card_le sub (by
      rw [card_erase_of_mem us]
      have ns : S.card=5 := size
      omega)
    exact (mem_filter.mp (show v∈inside G S u by
      rw [e]; exact mem_erase.mpr ⟨uv.symm,vs⟩)).2
  have clique : CompleteOn G S := by
    intro u us v vs uv
    exact (degree u v uv).elim (fun h=>hi u us h v vs uv)
      (fun h=>(hi v vs h u us uv.symm).symm)
  obtain ⟨xs,ax,bx⟩ := mem_filter.mp xk
  have sz : S.card=5 := size
  obtain ⟨y,ym⟩ := card_pos.mp (show 0<(S.erase x).card by rw [card_erase_of_mem xs]; omega)
  obtain ⟨yx,ys⟩ := mem_erase.mp ym
  have hy := (cut_mem_iff.mp (eq.symm ▸ ys)).2
  obtain ⟨p,pp,ps⟩ := path_between_in_clique S clique xs ys yx.symm
  have route : RouteOn G S x y := ⟨p,pp,ps⟩
  rcases hy with ay|by'
  · exact ⟨y,x,ay,bx,route.reverse⟩
  exact ⟨x,y,ax,by',route⟩

#print axioms terminal_route_at_five_vertex_all_port_shore
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
