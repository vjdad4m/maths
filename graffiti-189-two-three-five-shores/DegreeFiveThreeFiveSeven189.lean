import DegreeFiveThreeFiveShapes189
import ResidualOreParam189
import WingSignature189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset
open private Shore shore_off shore_closed shore_disjoint from DegreeFiveActualCut189
open private Cmp from DegreeFiveThreeForeignImpossible189
open private inside_high_at_least_four_if_exclusive inside_high_at_least_three from DegreeFiveBalancedCommonRoot189
open private nonport_neighbors_subset from DegreeFiveThreeFiveShapes189
open ArticulationPair
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

/-- On the seven-vertex three-port shore, remove only one universal
common vertex, irrespective of how many other common contacts there are. -/
theorem free_route_on_three_port_seven_shore
    (hc : G.Connected) (even : ∀ x,(EvenFrom G x).card≤6)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (min2 : ∀ u : V,2≤G.degree u)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (D5 : (cutPorts D).card=5) (seven : (Shore C).card=7)
    {x : V} (xc : x∈Shore C) (ax : G.Adj a x) (bx : G.Adj b x) :
    WingRealizes G a b (Shore C) .aFree ∨ WingRealizes G a b (Shore C) .bFree := by
  classical
  let S := Shore C
  let R := S.erase x
  have r6 : R.card=6 := by rw [card_erase_of_mem (show x∈S from xc)]; simp [S,seven]
  have int (u : V) (ur : u∈R) (uh : 5≤G.degree u) : 3≤(R.filter (G.Adj u)).card := by
    obtain ⟨ux,us⟩ := mem_erase.mp ur
    by_cases common : G.Adj a u ∧ G.Adj b u
    · have universal := common_universal_in_shore_at_five hc even cd us common.1 common.2 D5
      have eq : R.filter (G.Adj u)=R.erase u := by
        ext w
        constructor
        · intro h
          obtain ⟨wr,uw⟩ := mem_filter.mp h
          exact mem_erase.mpr ⟨uw.ne.symm,wr⟩
        intro h
        obtain ⟨wu,wr⟩ := mem_erase.mp h
        exact mem_filter.mpr ⟨wr,universal w (mem_of_mem_erase wr) wu.symm⟩
      rw [eq,card_erase_of_mem ur,r6]
      decide
    have a4 : 4≤(inside G S u).card := inside_high_at_least_four_if_exclusive us uh common
    have sub : (inside G S u).erase x⊆R.filter (G.Adj u) := by
      intro w wm
      obtain ⟨wx,wm⟩ := mem_erase.mp wm
      obtain ⟨ws,uw⟩ := mem_filter.mp wm
      exact mem_filter.mpr ⟨mem_erase.mpr ⟨wx,ws⟩,uw⟩
    have b := card_le_card sub
    have c : (inside G S u).card≤((inside G S u).erase x).card+1 := by
      by_cases hx : x∈inside G S u
      · rw [card_erase_of_mem hx]; omega
      rw [erase_eq_of_not_mem hx]; omega
    omega
  have pair (u : V) (ur : u∈R) (v : V) (vr : v∈R) (uv : u≠v) :
      3≤(R.filter (G.Adj u)).card ∨ 3≤(R.filter (G.Adj v)).card :=
    (degree u v uv).imp (int u ur) (int v vr)
  have xun := common_universal_in_shore_at_five hc even cd xc ax bx D5
  have xR : x∉R := by simp [R]
  have all : insert x R=S := insert_erase xc
  by_cases h : ∀ u∈R,(R.filter (G.Adj u)).card<3 → ∃ v∈R,G.Adj u v
  · obtain ⟨u,ur,v,vr,p⟩ := residual_route_if_low_not_isolated_at_d 3 R (by omega)
      (card_pos.mp (by omega)) pair h
    have xu := xun u (mem_of_mem_erase ur) (mem_erase.mp ur).1.symm
    exact .inl ⟨x,v,ax,show RouteOn G S x v from all ▸ p.prefix xu xR⟩
  push_neg at h
  obtain ⟨z,zr,zd,iso⟩ := h
  have zs : z∈S := mem_of_mem_erase zr
  have zx : z≠x := (mem_erase.mp zr).1
  have port : z∈cutPorts C := by
    apply Classical.byContradiction
    intro no
    have sub : G.neighborFinset z⊆{x} := by
      intro w hw
      have wz := (nonport_neighbors_subset zs no) hw
      have edge := (mem_neighborFinset G z w).mp hw
      apply mem_singleton.mpr
      apply Classical.byContradiction
      intro wx
      exact iso w (mem_erase.mpr ⟨wx,mem_of_mem_erase wz⟩) edge
    have c := card_le_card sub
    rw [card_neighborFinset_eq_degree,card_singleton] at c
    have t := min2 z
    omega
  let Q := R.erase z
  have hi (u : V) (uq : u∈Q) : 3≤(Q.filter (G.Adj u)).card := by
    obtain ⟨uz,ur⟩ := mem_erase.mp uq
    have eq : Q.filter (G.Adj u)=R.filter (G.Adj u) := by
      ext w
      by_cases e : w=z
      · subst w; simp [Q,show ¬G.Adj u z from fun e=>iso u ur e.symm]
      simp [Q,e]
    rw [eq]
    exact (pair z zr u ur uz.symm).resolve_left (by omega)
  have q5 : Q.card=5 := by rw [card_erase_of_mem (show z∈R from zr),r6]
  obtain ⟨r,rq⟩ := card_pos.mp (show 0<Q.card by omega)
  obtain ⟨t,tQ,p⟩ := rooted_high_residual_Ore_at_d 3 Q (by omega) hi rq
  have tr : t∈R := mem_of_mem_erase tQ
  have xt := xun t (mem_of_mem_erase tr) (mem_erase.mp tr).1.symm
  have xz := xun z zs zx.symm
  have noX : x∉Q := fun h=>xR (mem_of_mem_erase h)
  have noZ : z∉insert x Q := by simp [Q,zx]
  have eq : insert z (insert x Q)=S := by
    have swap : insert z (insert x Q)=insert x (insert z Q) := by ext w; simp [or_left_comm]
    rw [swap,insert_erase zr,all]
  have full : RouteOn G S r z := eq ▸ ((p.suffix xt.symm noX).suffix xz noZ)
  rcases (mem_filter.mp port).2 with az|bz
  · exact .inl ⟨z,r,az,full.reverse⟩
  exact .inr ⟨z,r,bz,full.reverse⟩

#print axioms free_route_on_three_port_seven_shore
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
