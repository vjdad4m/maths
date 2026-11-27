import DegreeFiveBothFiveRooted189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph Finset
open private Shore shore_off shore_disjoint from DegreeFiveActualCut189
open private Cmp from DegreeFiveThreeForeignImpossible189
open private sharedPortSet from DegreeFiveBalancedCommonRoot189
open private common_sub_ports from DegreeFiveBothFiveResidual189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

private theorem splice_common_terminal_and_rooted
    (ab : a≠b) {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    {w x y z : V} (aw : G.Adj a w) (bx : G.Adj b x) (by' : G.Adj b y)
    (terminal : RouteOn G (Shore C) w x) (rooted : RouteOn G (Shore D) y z) :
    ∃ r t : V,∃ q : G.Walk r t,q.IsPath ∧ ∀ p,p∈q.support := by
  have base := terminal.prefix aw (shore_off C).1
  have ext := base.suffix bx.symm (fun h=>(mem_insert.mp h).elim ab.symm (shore_off C).2)
  have apart : Disjoint (insert b (insert a (Shore C))) (Shore D) := by
    apply disjoint_left.mpr
    intro v vc vd
    rcases mem_insert.mp vc with rfl|vc
    · exact (shore_off D).2 vd
    rcases mem_insert.mp vc with rfl|vc
    · exact (shore_off D).1 vd
    exact disjoint_left.mp (shore_disjoint cd) vc vd
  obtain ⟨p,pp,ps⟩ := ext.join rooted apart by'
  refine ⟨a,z,p,pp,fun t=>(ps t).mpr ?_⟩
  rcases cover t with rfl|rfl|tc|td
  · simp
  · simp
  · exact mem_union_left _ (mem_insert_of_mem (mem_insert_of_mem tc))
  exact mem_union_right _ td

/-- Both-common saturated 5+5 profiles are traceable when both shores
have at least three common porters. No graph census is used. -/
theorem traceable_at_both_five_port_shores_with_three_shared
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card  ≤  6)
    (degree : ∀ u v : V,u≠v → 5  ≤  G.degree u ∨ 5  ≤  G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    (C5 : (cutPorts C).card=5) (D5 : (cutPorts D).card=5)
    (C3 : 3  ≤  (sharedPortSet C).card) (D3 : 3  ≤  (sharedPortSet D).card) :
    ∃ r t : V,∃ q : G.Walk r t,q.IsPath ∧ ∀ p,p∈q.support := by
  classical
  obtain ⟨x,xk⟩ := card_pos.mp (show 0<(sharedPortSet C).card by omega)
  obtain ⟨y,yk⟩ := card_pos.mp (show 0<(sharedPortSet D).card by omega)
  obtain ⟨xc,ax,bx⟩ := mem_filter.mp xk
  obtain ⟨yd,ay,by'⟩ := mem_filter.mp yk
  have Cms : 5 ≤ (Shore C).card := by
    rw [←C5]
    exact card_le_card (filter_subset _ _)
  have Dms : 5 ≤ (Shore D).card := by
    rw [←D5]
    exact card_le_card (filter_subset _ _)
  have kC : (sharedPortSet C).card  ≤  5 := (card_le_card (common_sub_ports C)).trans (le_of_eq C5)
  have kD : (sharedPortSet D).card  ≤  5 := (card_le_card (common_sub_ports D)).trans (le_of_eq D5)
  have uniC (u : V) (uk : u∈sharedPortSet C) : ∀ w∈Shore C,u≠w → G.Adj u w := by
    obtain ⟨uc,au,bu⟩ := mem_filter.mp uk
    exact common_universal_in_shore_at_five hc even cd uc au bu D5
  have uniD (u : V) (uk : u∈sharedPortSet D) : ∀ w∈Shore D,u≠w → G.Adj u w := by
    obtain ⟨ud,au,bu⟩ := mem_filter.mp uk
    exact common_universal_in_shore_at_five hc even cd.symm ud au bu C5
  obtain ⟨lim,bound⟩ := both_five_shore_order_weighted hc two even cd xc ax bx yd ay by' C5 D5
  have roomC : (Shore C).card  ≤  2*(sharedPortSet C).card+2 := by omega
  have roomD : (Shore D).card  ≤  2*(sharedPortSet D).card+2 := by omega
  obtain ⟨u,Rc,Rcu⟩ := rooted_route_at_five_port_shore_with_big_shared degree C5 C3
    (by omega) roomC xk uniC
  obtain ⟨v,Rd,Rdv⟩ := rooted_route_at_five_port_shore_with_big_shared degree D5 D3
    (by omega) roomD yk uniD
  have ab : a≠b := by intro e; rw [e,SimpleGraph.dist_self] at two; omega
  by_cases Cterm : (Shore C).card  ≤  2*(sharedPortSet C).card
  · exact splice_common_terminal_and_rooted ab cd cover ax (mem_filter.mp (Rcu Cterm)).2.2
      by' Rc Rd
  have Dterm : (Shore D).card  ≤  2*(sharedPortSet D).card := by omega
  have cover' (w : V) : w=a ∨ w=b ∨ w∈Shore D ∨ w∈Shore C :=
    (cover w).imp id (fun h=>h.imp id Or.symm)
  exact splice_common_terminal_and_rooted ab cd.symm cover' ay (mem_filter.mp (Rdv Dterm)).2.2
    bx Rd Rc

#print axioms traceable_at_both_five_port_shores_with_three_shared
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
