import DegreeFiveBothFiveClique189
import DegreeFiveBothFiveClose189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph Finset
open private Shore shore_off shore_disjoint from DegreeFiveActualCut189
open private Cmp from DegreeFiveThreeForeignImpossible189
open private sharedPortSet from DegreeFiveBalancedCommonRoot189
open private cut_mem_iff common_sub_ports from DegreeFiveBothFiveResidual189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

private theorem splice_terminal_onto_port
    (ab : a≠b) {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    {u v x y : V} (au : G.Adj a u) (bv : G.Adj b v) (xp : x∈cutPorts D)
    (terminal : RouteOn G (Shore C) u v) (rooted : RouteOn G (Shore D) x y) :
    ∃ r t : V,∃ q : G.Walk r t,q.IsPath ∧ ∀ p,p∈q.support := by
  have base := terminal.prefix au (shore_off C).1
  have mid := base.suffix bv.symm (fun h=>(mem_insert.mp h).elim ab.symm (shore_off C).2)
  have apart : Disjoint (insert b (insert a (Shore C))) (Shore D) := by
    apply disjoint_left.mpr
    intro v vc vd
    rcases mem_insert.mp vc with rfl|vc
    · exact (shore_off D).2 vd
    rcases mem_insert.mp vc with rfl|vc
    · exact (shore_off D).1 vd
    exact disjoint_left.mp (shore_disjoint cd) vc vd
  have pack {r : V} (p : RouteOn G (insert b (insert a (Shore C))∪Shore D) r y) :
      ∃ r t : V,∃ q : G.Walk r t,q.IsPath ∧ ∀ w,w∈q.support := by
    obtain ⟨q,qp,qs⟩ := p
    refine ⟨r,y,q,qp,fun w=>(qs w).mpr ?_⟩
    rcases cover w with rfl|rfl|wc|wd
    · simp
    · simp
    · exact mem_union_left _ (mem_insert_of_mem (mem_insert_of_mem wc))
    exact mem_union_right _ wd
  rcases (cut_mem_iff.mp xp).2 with ax|bx
  · exact pack (mid.reverse.join rooted apart ax)
  exact pack (mid.join rooted apart bx)

/-- Distance-two two-shore cuts with five porters on each and a common
porter on each are traceable, for any positive common counts. -/
theorem traceable_at_both_five_port_shores
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card  ≤  6)
    (degree : ∀ u v : V,u≠v → 5  ≤  G.degree u ∨ 5  ≤  G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    (C5 : (cutPorts C).card=5) (D5 : (cutPorts D).card=5)
    {x y : V} (xc : x∈Shore C) (ax : G.Adj a x) (bx : G.Adj b x)
    (yd : y∈Shore D) (ay : G.Adj a y) (by' : G.Adj b y) :
    ∃ r t : V,∃ q : G.Walk r t,q.IsPath ∧ ∀ p,p∈q.support := by
  classical
  let K := sharedPortSet C
  let L := sharedPortSet D
  have xk : x∈K := mem_filter.mpr ⟨xc,ax,bx⟩
  have yk : y∈L := mem_filter.mpr ⟨yd,ay,by'⟩
  by_cases both : 3  ≤  K.card ∧ 3  ≤  L.card
  · exact traceable_at_both_five_port_shores_with_three_shared hc two even degree cd cover C5 D5
      both.1 both.2
  have cs : 5  ≤  (Shore C).card := by rw [←C5]; exact card_le_card (filter_subset _ _)
  have ds : 5  ≤  (Shore D).card := by rw [←D5]; exact card_le_card (filter_subset _ _)
  have k5 : K.card  ≤  5 := (card_le_card (common_sub_ports C)).trans (le_of_eq C5)
  have l5 : L.card  ≤  5 := (card_le_card (common_sub_ports D)).trans (le_of_eq D5)
  have uniC (u : V) (uk : u∈K) : ∀ w∈Shore C,u≠w → G.Adj u w := by
    obtain ⟨uc,au,bu⟩ := mem_filter.mp uk
    exact common_universal_in_shore_at_five hc even cd uc au bu D5
  have uniD (u : V) (uk : u∈L) : ∀ w∈Shore D,u≠w → G.Adj u w := by
    obtain ⟨ud,au,bu⟩ := mem_filter.mp uk
    exact common_universal_in_shore_at_five hc even cd.symm ud au bu C5
  obtain ⟨_,wgt⟩ := both_five_shore_order_weighted hc two even cd xc ax bx yd ay by' C5 D5
  change 2*((Shore C).card+(Shore D).card) ≤ 18+K.card+L.card at wgt
  have total : (Shore C).card+(Shore D).card ≤ 12 := by
    by_cases k : 3 ≤ K.card
    · have q : L.card<3 := Nat.lt_of_not_ge (fun h=>both ⟨k,h⟩)
      omega
    omega
  have ab : a≠b := by intro e; rw [e,SimpleGraph.dist_self] at two; omega
  have cover' (w : V) : w=a ∨ w=b ∨ w∈Shore D ∨ w∈Shore C :=
    (cover w).imp id (fun h=>h.imp id Or.symm)
  obtain ⟨cr,crp,cend,rc⟩ := rooted_port_route_at_small_five_shore degree C5 (by omega) xk uniC
  obtain ⟨dr,drp,dend,rd⟩ := rooted_port_route_at_small_five_shore degree D5 (by omega) yk uniD
  by_cases c5 : (Shore C).card=5
  · obtain ⟨u,v,au,bv,p⟩ := terminal_route_at_five_vertex_all_port_shore degree C5 c5 xk uniC
    exact splice_terminal_onto_port ab cd cover au bv drp p rd
  by_cases d5 : (Shore D).card=5
  · obtain ⟨u,v,au,bv,p⟩ := terminal_route_at_five_vertex_all_port_shore degree D5 d5 yk uniD
    exact splice_terminal_onto_port ab cd.symm cover' au bv crp p rc
  by_cases k3 : 3 ≤ K.card
  · obtain ⟨u,route,stop⟩ := rooted_route_at_five_port_shore_with_big_shared degree C5 k3
      (by omega) (by change (Shore C).card ≤ 2*K.card+2; omega) xk uniC
    have uk := stop (by change (Shore C).card ≤ 2*K.card; omega)
    exact splice_terminal_onto_port ab cd cover ax (mem_filter.mp uk).2.2 drp route rd
  have l3 : 3 ≤ L.card := by omega
  obtain ⟨v,route,stop⟩ := rooted_route_at_five_port_shore_with_big_shared degree D5 l3
      (by omega) (by change (Shore D).card ≤ 2*L.card+2; omega) yk uniD
  have vk := stop (by change (Shore D).card ≤ 2*L.card; omega)
  exact splice_terminal_onto_port ab cd.symm cover' ay (mem_filter.mp vk).2.2 crp route rc

#print axioms traceable_at_both_five_port_shores
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
