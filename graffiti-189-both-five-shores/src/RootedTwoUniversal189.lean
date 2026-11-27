import ResidualFourPath189
import UniversalRouteSingletons189

namespace Graffiti189LongestPath.CrossSaturation
open SimpleGraph Finset
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

/-- Two universal vertices can absorb a residue of at most five vertices
whose induced degree is at least two apart from at most one exception. -/
theorem rooted_route_with_two_universal
    (K R : Finset V) (k2 : K.card=2) (r5 : R.card≤5)
    {x : V} (xk : x∈K) (apart : Disjoint K R)
    (join : ∀ u∈K,∀ w∈K∪R,u≠w → G.Adj u w)
    (degree : ∀ u∈R,∀ v∈R,u≠v →
      2≤(R.filter (G.Adj u)).card ∨ 2≤(R.filter (G.Adj v)).card) :
    ∃ y,RouteOn G (K∪R) x y := by
  classical
  by_cases enough : R.card≤K.card
  · obtain ⟨y,p,_⟩ := universal_route_from_singletons K R xk apart join enough
    exact ⟨y,p⟩
  have block {P : Finset V} (pr : P⊆R) (room : R.card≤P.card+1) {u v : V}
      (up : u∈P) (vp : v∈P) (route : RouteOn G P u v) :
      ∃ y,RouteOn G (K∪R) x y := by
    have count := card_sdiff_add_card_eq_card pr
    obtain ⟨y,p,_⟩ := universal_route_with_one_block K R P xk up vp apart pr route join (by omega)
    exact ⟨y,p⟩
  by_cases full : R.card=5
  · obtain ⟨P,pr,pc,u,up,v,vp,p⟩ := four_path_in_five_with_pair_degree_two R full degree
    exact block pr (by omega) up vp p
  obtain ⟨u,ur,v,vr,uv⟩ := one_lt_card.mp (show 1<R.card by omega)
  obtain ⟨x',xr,xh⟩ : ∃ x∈R,1<(R.filter (G.Adj x)).card := by
    rcases degree u ur v vr uv with h|h
    · exact ⟨u,ur,by omega⟩
    exact ⟨v,vr,by omega⟩
  obtain ⟨i,ip,j,jp,ij⟩ := one_lt_card.mp xh
  obtain ⟨ir,xi⟩ := mem_filter.mp ip
  obtain ⟨jr,xj⟩ := mem_filter.mp jp
  let P : Finset V := {i,x',j}
  have sub : P⊆R := insert_subset_iff.mpr ⟨ir,insert_subset_iff.mpr ⟨xr,singleton_subset_iff.mpr jr⟩⟩
  have p3 : P.card=3 := by
    have off : i∉({x',j} : Finset V) := by simp [xi.ne.symm,ij]
    change (insert i ({x',j} : Finset V)).card=3
    rw [card_insert_of_not_mem off]
    simp [xj.ne]
  exact block sub (by omega) (by simp [P]) (by simp [P]) (RouteOn.three xi.symm xj ij)

#print axioms rooted_route_with_two_universal
end Graffiti189LongestPath.CrossSaturation
