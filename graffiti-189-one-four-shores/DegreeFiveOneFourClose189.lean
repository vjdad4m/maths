import DegreeFiveFreeOreSmallNear189
import DegreeFiveOneFourShapes189
import UniversalRouteSingletons189



namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset
open private Shore shore_off shore_closed shore_disjoint from DegreeFiveActualCut189
open private Cmp from DegreeFiveThreeForeignImpossible189
open private inside_high_at_least_four_if_exclusive inside_high_at_least_three from DegreeFiveBalancedCommonRoot189
open private cut_mem_iff from DegreeFiveBothFiveResidual189
open private shore_connected from DegreeFiveActualCut189
open private lift_side_path from DegreeFiveSmallSides189
open ArticulationPair
open private nonport_neighbors_subset from DegreeFiveThreeFiveShapes189
open private secondShore from DegreeFiveDistanceTwoThreeClose189
open private sharedPortSet from DegreeFiveBalancedCommonRoot189
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

theorem free_all_high_four_port_shore_at_most_eight
    {D : Cmp (G:=G) (a:=a) (b:=b)}
    (four : (cutPorts D).card=4) (small : (Shore D).card≤8)
    (high : ∀ u∈Shore D,5≤G.degree u)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v) :
    WingRealizes G a b (Shore D) .aFree ∨ WingRealizes G a b (Shore D) .bFree := by
  classical
  by_cases tiny : (Shore D).card≤6
  · exact free_port_route_at_most_six degree (by omega) tiny
  let S := Shore D
  let U := ↑(↑S : Set V)
  let J := G.induce (↑S : Set V)
  let P : Finset U := univ.filter (fun u=>u.val∈cutPorts D)
  let K : Finset U := univ\P
  have ps (u : U) : u∈P ↔ u.val∈cutPorts D := by simp [P]
  have ks (u : U) : u∈K ↔ u.val∉cutPorts D := by simp [K,ps]
  have pk : P.card=4 := by
    rw [←four]
    apply card_bij (fun u _=>u.val)
    · intro u h; exact (ps u).mp h
    · intro u _ v _ e; exact Subtype.ext e
    intro w wP
    exact ⟨⟨w,(cut_mem_iff.mp wP).1⟩,(ps _).mpr wP,rfl⟩
  have n : Fintype.card U=S.card := Fintype.card_coe S
  have cap : Fintype.card U≤8 := n.trans_le small
  have large : 7≤Fintype.card U := by
    have h : ¬S.card≤6 := tiny
    omega
  have tally : K.card+P.card=Fintype.card U :=
    (card_sdiff_add_card_eq_card (subset_univ P)).trans card_univ
  let H : SimpleGraph U :=
    ⟨fun u v=>J.Adj u v ∨ (u≠v ∧ (u∈K ∨ v∈K)),
    by intro u v; rintro (h|⟨n,m⟩); exact .inl h.symm; exact .inr ⟨n.symm,m.symm⟩,
    by intro u; rintro (h|⟨n,_⟩); exact J.loopless _ h; exact n rfl⟩
  letI : DecidableRel H.Adj := Classical.decRel _
  have low (u : U) : 3≤J.degree u := by
    change 3≤(G.induce (↑S : Set V)).degree u
    rw [←inside_card_eq_degree_induce (G:=G) S u]
    exact inside_high_at_least_three u.property (high u.val u.property)
  have inner (u : U) (ku : u∈K) : 5≤J.degree u := by
    change 5≤(G.induce (↑S : Set V)).degree u
    rw [←inside_card_eq_degree_induce (G:=G) S u]
    have sub := nonport_neighbors_subset u.property ((ks u).mp ku)
    have sub' : G.neighborFinset u.val⊆inside G S u.val := fun w hw=>
      mem_filter.mpr ⟨mem_of_mem_erase (sub hw),(mem_neighborFinset G u.val w).mp hw⟩
    have q := card_le_card sub'
    rw [card_neighborFinset_eq_degree] at q
    exact (high u.val u.property).trans q
  have sub : J≤H := fun _ _ h=>.inl h
  have safe (u v : U) (h : H.Adj u v) (no : ¬J.Adj u v) :
      Fintype.card U≤J.degree u+J.degree v := by
    rcases (Or.resolve_left h no).2 with uK|vK
    · have p := inner u uK
      have q := low v
      omega
    have p := low u
    have q := inner v vK
    omega
  obtain ⟨r,rp⟩ := card_pos.mp (show 0<P.card by omega)
  obtain ⟨u,uk⟩ := card_pos.mp (show 0<K.card by omega)
  let R := P.erase r
  have r3 : R.card=3 := by rw [card_erase_of_mem (show r∈P from rp),pk]
  have dis : Disjoint K R := disjoint_left.mpr fun w wk wr=>
    (mem_sdiff.mp wk).2 (mem_of_mem_erase wr)
  have join (v : U) (vk : v∈K) (w : U) (_ : w∈K∪R) (vw : v≠w) : H.Adj v w :=
    .inr ⟨vw,.inl vk⟩
  obtain ⟨t,p,_⟩ := universal_route_from_singletons K R uk dis join (by omega)
  have off : r∉K∪R := by
    intro rm
    exact (mem_union.mp rm).elim (fun h=>(mem_sdiff.mp h).2 rp)
      (fun h=>(mem_erase.mp h).1 rfl)
  have ru : r≠u := fun h=>off (mem_union_left _ (h.symm ▸ uk))
  have hp : H.Adj r u := .inr ⟨ru,.inr uk⟩
  have all : insert r (K∪R)=(univ : Finset U) := by
    rw [←union_insert,insert_erase rp,union_comm]
    exact union_sdiff_of_subset (subset_univ _)
  have path : RouteOn H univ r t := all ▸ p.prefix hp off
  obtain ⟨q,qp,qs⟩ := path
  obtain ⟨w,p,pp,pS⟩ := Graffiti189Ore.rooted_closure sub r safe
    ⟨t,q,qp,fun v=>(qs v).mpr (mem_univ _)⟩
  have actual : RouteOn G S r.val w.val := lift_side_path S p pp pS
  rcases (cut_mem_iff.mp ((ps r).mp rp)).2 with ar|br
  · exact .inl ⟨r.val,w.val,ar,actual⟩
  exact .inr ⟨r.val,w.val,br,actual⟩

theorem traceable_of_actual_five_one_four_ports
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    (one : (cutPorts C).card=1) (four : (cutPorts D).card=4) :
    ∃ r t : V,∃ q : G.Walk r t,q.IsPath ∧ ∀ p,p∈q.support := by
  classical
  have ab : a≠b := by intro h; rw [h,dist_self] at two; omega
  obtain ⟨r,e,ar,br,high,small⟩ := one_four_shore_shape hc two even conn degree cd cover one four
  have mid : WingRealizes G a b (Shore C) .terminal := by
    rw [e]
    exact ⟨r,r,ar,br,RouteOn.singleton⟩
  exact traceable_of_complementary_wings ab (shore_disjoint cd) (shore_off C).1 (shore_off C).2
    (shore_off D).1 (shore_off D).2 cover (.inl ⟨mid,free_all_high_four_port_shore_at_most_eight four small high degree⟩)

#print axioms free_all_high_four_port_shore_at_most_eight
#print axioms traceable_of_actual_five_one_four_ports
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
