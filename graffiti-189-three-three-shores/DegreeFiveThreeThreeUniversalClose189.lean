import DegreeFiveThreeThreeDarkRoute189
import DegreeFiveFourSmallTermGeneric189







namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset
open private Shore shore_off shore_closed shore_disjoint shore_nonempty shore_connected shore_hit_a shore_hit_b from DegreeFiveActualCut189
open private two_walk_middle from DistanceTwoCut189
open private secondShore from DegreeFiveDistanceTwoThreeClose189
open private Cmp two_shore_budget count_cut_degree_on_two_shores portColor from DegreeFiveThreeForeignImpossible189
open private four_in_nonsingleton second_positive_of_small_ports anywhere_high_of_two from DegreeFiveDistanceTwoThreeClose189
open private nonport_neighbors_subset nonport_degree_bound_small from DegreeFiveThreeFiveShapes189
open private nonport_mem_second_iff_neighbor_port from DegreeFiveOneFiveFarProfile189
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

open private boundary_has_at_least_two dark dark_boundary_is_visible visible_in_nonports
  from DegreeFiveTwoThreeBase189

open private firstDark firstDark_iff_distance_three dark_dist_ge_three cross_ports_at_distance_two
  distance_two_at_cut_lower from DegreeFiveTwoThreeVisTwo189
open private visible_at_least_two_of_dark from DegreeFiveTwoThreeBase189

open ArticulationPair
open private inside_high_at_least_four_if_exclusive from DegreeFiveBalancedCommonRoot189
open private visible_touches_some_port all_high_port_neighborhood high_visible_neighborhood
  from DegreeFiveThreeThreeDegreeHelpers189

private theorem terminal_route_on_all_high_six_with_three_ports
    {C : Cmp (G:=G) (a:=a) (b:=b)}
    (C3 : (cutPorts C).card=3) (six : (Shore C).card=6)
    (high : ∀ z∈Shore C,5≤G.degree z)
    {x y : V} (xp : x∈cutPorts C) (yp : y∈cutPorts C) (xy : x≠y) :
    RouteOn G (Shore C) x y := by
  classical
  let P := cutPorts C
  let S := Shore C
  let A := S\P
  have ap : A.card+P.card=S.card := card_sdiff_add_card_eq_card (filter_subset _ _)
  have a3 : A.card=3 := by
    have pp : P.card=3 := C3
    have ss : S.card=6 := six
    omega
  obtain ⟨u,v,w,uv,uw,vw,ae⟩ := card_eq_three.mp a3
  have uA : u∈A := by simp [ae]
  have vA : v∈A := by simp [ae]
  have wA : w∈A := by simp [ae]
  have rest : ∃ t∈P,t≠x ∧ t≠y := by
    apply Classical.byContradiction
    intro no
    have sub : P⊆({x,y} : Finset V) := by
      intro t tp
      apply Classical.byContradiction
      intro out
      exact no ⟨t,tp,fun e=>out (by simp [e]),fun e=>out (by simp [e])⟩
    have b := card_le_card sub
    have c : ({x,y} : Finset V).card=2 := by simp [xy]
    have pp : P.card=3 := C3
    omega
  obtain ⟨t,tp,tx,ty⟩ := rest
  have pe : P={x,y,t} := by
    have sub : ({x,y,t} : Finset V)⊆P := insert_subset_iff.mpr ⟨xp,insert_subset_iff.mpr
      ⟨yp,singleton_subset_iff.mpr tp⟩⟩
    have c : ({x,y,t} : Finset V).card=3 := by simp [xy,tx.symm,ty.symm]
    have pp : P.card=3 := C3
    exact (eq_of_subset_of_card_le sub (by omega)).symm
  have sSub : P⊆S := filter_subset _ _
  have universal (u : V) (uA : u∈A) (z : V) (zs : z∈S) (uz : u≠z) : G.Adj u z := by
    obtain ⟨us,up⟩ := mem_sdiff.mp uA
    have sub := nonport_neighbors_subset us up
    have e : G.neighborFinset u=S.erase u := eq_of_subset_of_card_le sub (by
      rw [card_neighborFinset_eq_degree,card_erase_of_mem us]
      have hi := high u us
      have n : S.card=6 := six
      omega)
    exact (mem_neighborFinset G u z).mp (e.symm ▸ mem_erase.mpr ⟨uz.symm,zs⟩)
  have no (u : V) (hm : u∈A) (p : V) (hp : p∈P) : u≠p :=
    fun e=>(mem_sdiff.mp hm).2 (e.symm ▸ hp)
  have A_sub : A⊆S := sdiff_subset
  have p₀ := RouteOn.three (universal u uA x (sSub xp) (no u uA x xp)).symm
    (universal u uA t (sSub tp) (no u uA t tp)) tx.symm
  have p₁ := p₀.suffix (universal v vA t (sSub tp) (no v vA t tp)).symm
    (by simp [no v vA x xp,no v vA t tp,uv.symm])
  have p₂ := p₁.suffix (universal v vA w (A_sub wA) vw)
    (by simp [no w wA x xp,no w wA t tp,uw.symm,vw.symm])
  have p₃ := p₂.suffix (universal w wA y (sSub yp) (no w wA y yp))
    (by simp [xy.symm,(no w wA y yp).symm,(no v vA y yp).symm,
      (no u uA y yp).symm,ty.symm])
  have cover : P∪A=S := union_sdiff_of_subset sSub
  have eq : insert y (insert w (insert v ({x,u,t} : Finset V)))=S := by
    rw [←cover,pe,ae]
    ext z
    simp [or_comm,or_left_comm,or_assoc]
  change RouteOn G S x y
  exact eq ▸ p₃

private theorem universal_three_three_join_small_shore
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    (C3 : (cutPorts C).card=3) (D3 : (cutPorts D).card=3)
    (allC : ∀ z∈cutPorts C,G.Adj a z) (allD : ∀ z∈cutPorts D,G.Adj a z)
    (D4 : (Shore D).card=4) (A3 : (secondShore C a).card=3)
    (high : ∀ z∈Shore C,5≤G.degree z) :
    ∃ x y,∃ p : G.Walk x y,p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  have ab : a≠b := by intro h; rw [h,dist_self] at two; omega
  let K := Shore D\cutPorts D
  have k1 : K.card=1 := by
    have n : K.card+(cutPorts D).card=(Shore D).card := card_sdiff_add_card_eq_card (filter_subset _ _)
    omega
  obtain ⟨z,zk⟩ := card_pos.mp (show 0<K.card by omega)
  obtain ⟨zd,zp⟩ := mem_sdiff.mp zk
  have zLow : ¬5≤G.degree z := by
    have h := nonport_degree_bound_small zd zp
    omega
  obtain ⟨v,vp⟩ := card_pos.mp (show 0<(cutPorts D).card by omega)
  have vd := (mem_filter.mp vp).1
  have vhigh := (degree v z (fun e=>zp (e ▸ vp))).resolve_right zLow
  have bv : G.Adj b v := by
    apply Classical.byContradiction
    intro no
    have p := inside_high_at_least_four_if_exclusive vd vhigh (fun h=>no h.2)
    have sub : inside G (Shore D) v⊆(Shore D).erase v := by
      intro t tN
      obtain ⟨td,vt⟩ := mem_filter.mp tN
      exact mem_erase.mpr ⟨vt.ne.symm,td⟩
    have q := card_le_card sub
    rw [card_erase_of_mem vd,D4] at q
    omega
  obtain ⟨j,k,aj,_,pathD⟩ := terminal_route_on_four_vertices_with_two_ports degree
    (show 2≤(cutPorts D).card by omega) D4 vd (allD v vp) bv
  have fd : WingRealizes G a b (Shore D) .aFree := ⟨j,k,aj,pathD⟩
  have term : WingRealizes G a b (Shore C) .terminal := by
    by_cases np : (dark C).Nonempty
    · have vis : 1≤(secondShore D a).card := by
        obtain ⟨x,xp⟩ := card_pos.mp (show 0<(cutPorts D).card by omega)
        have g := four_in_nonsingleton degree (show 2≤(Shore D).card by omega)
        exact second_positive_of_small_ports (shore_off D).1 ⟨x,(mem_filter.mp xp).1,allD x xp⟩
          hc g (by omega) (.inl rfl)
      exact terminal_of_three_visible_and_dark_nonempty hc two even cd C3 D3 allC allD vis A3 high np
    have qNil : dark C=∅ := Finset.eq_empty_iff_forall_not_mem.mpr (fun x hx=>np ⟨x,hx⟩)
    have sum := card_sdiff_add_card_eq_card (visible_in_nonports allC)
    change (dark C).card+(secondShore C a).card=(Shore C\cutPorts C).card at sum
    rw [qNil,card_empty,A3] at sum
    have tally := card_sdiff_add_card_eq_card (show cutPorts C⊆Shore C from filter_subset _ _)
    have six : (Shore C).card=6 := by omega
    have bH : 5≤G.degree b := (degree b z
      (fun e=>(shore_off D).2 (Eq.mp (congrArg (fun t : V=>t∈Shore D) e.symm) zd))).resolve_right zLow
    have count := count_cut_degree_on_two_shores cd cover two (.inr rfl : b=a ∨ b=b)
    have dB : (portColor D b).card≤3 := by
      have sub : portColor D b⊆cutPorts D := by
        intro t h
        obtain ⟨td,bt⟩ := mem_filter.mp h
        exact mem_filter.mpr ⟨td,.inr bt⟩
      exact (card_le_card sub).trans D3.le
    obtain ⟨y,yp⟩ := card_pos.mp (show 0<(portColor C b).card by omega)
    obtain ⟨yc,by'⟩ := mem_filter.mp yp
    have yP : y∈cutPorts C := mem_filter.mpr ⟨yc,.inr by'⟩
    have other : ∃ x∈cutPorts C,x≠y := by
      apply Classical.byContradiction
      intro no
      have sub : cutPorts C⊆{y} := fun u up=>mem_singleton.mpr
        (Classical.byContradiction (fun e=>no ⟨u,up,e⟩))
      have tally := card_le_card sub
      rw [C3,card_singleton] at tally
      omega
    obtain ⟨x,xp,xy⟩ := other
    exact ⟨x,y,allC x xp,by',terminal_route_on_all_high_six_with_three_ports C3 six high xp yP xy⟩
  exact traceable_of_complementary_wings ab (shore_disjoint cd) (shore_off C).1 (shore_off C).2
    (shore_off D).1 (shore_off D).2 cover (.inl ⟨term,.inl fd⟩)

theorem traceable_of_actual_five_three_three_universal_cut
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    (C3 : (cutPorts C).card=3) (D3 : (cutPorts D).card=3)
    (allC : ∀ z∈cutPorts C,G.Adj a z) (allD : ∀ z∈cutPorts D,G.Adj a z) :
    ∃ x y,∃ p : G.Walk x y,p.IsPath ∧ ∀ z,z∈p.support := by
  rcases three_three_universal_cut_shape hc two even conn degree cd C3 D3 allC allD with
    ⟨c4,dvis,high⟩|⟨d4,cvis,high⟩
  · exact universal_three_three_join_small_shore hc two even degree cd.symm
      (fun z=>(cover z).imp id (fun h=>h.imp id Or.symm)) D3 C3 allD allC c4 dvis high
  exact universal_three_three_join_small_shore hc two even degree cd cover C3 D3 allC allD d4 cvis high

#print axioms traceable_of_actual_five_three_three_universal_cut
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
