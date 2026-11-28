import DegreeFiveTwoThreeVisTwo189





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

open private dark_dist_ge_three firstDark firstDark_iff_distance_three cross_ports_at_distance_two
  distance_two_at_cut_lower from DegreeFiveTwoThreeVisTwo189
open private visible_at_least_two_of_dark from DegreeFiveTwoThreeBase189

theorem no_three_visible_on_two_port_shore
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (C2 : (cutPorts C).card=2) (D3 : (cutPorts D).card=3)
    (allC : ∀ z∈cutPorts C,G.Adj a z) (allD : ∀ z∈cutPorts D,G.Adj a z)
    (Dpos : 1≤(secondShore D a).card) (Qpos : (dark C).Nonempty)
    (A3 : (secondShore C a).card=3) :
    False := by
  classical
  let A := secondShore C a
  let Q := dark C
  let P := cutPorts C
  have a3 : A.card=3 := A3
  have qpos : Q.Nonempty := Qpos
  have lo := distance_two_at_cut_lower two cd
  have cap := distanceTwo_le_of_even 5 a (even a)
  have satD : (secondShore D a).card=1 := by omega
  have aD2 : (DistanceTwo G a).card=5 := by omega
  have DE : dark D=∅ := by
    apply card_eq_zero.mp
    apply Classical.byContradiction
    intro n
    have h := visible_at_least_two_of_dark hc conn allD (card_pos.mp (by omega))
    omega
  have d4 : (Shore D).card=4 := by
    have s := visible_in_nonports allD
    have t := card_sdiff_add_card_eq_card s
    change (dark D).card+(secondShore D a).card=(Shore D\cutPorts D).card at t
    rw [DE,card_empty,satD] at t
    have h : (Shore D\cutPorts D).card+(cutPorts D).card=(Shore D).card :=
      card_sdiff_add_card_eq_card (filter_subset _ _)
    omega
  obtain ⟨w,wv⟩ := card_pos.mp (show 0<(secondShore D a).card by omega)
  obtain ⟨wd,wp⟩ := mem_sdiff.mp (visible_in_nonports allD wv)
  have wLow : ¬5≤G.degree w := by
    have h := nonport_degree_bound_small wd wp
    omega
  have high (z : V) (zc : z∈Shore C) : 5≤G.degree z :=
    (degree z w (fun e=>disjoint_left.mp (shore_disjoint cd) zc (e ▸ wd))).resolve_right wLow
  have Qc : Q⊆Shore C := fun _ h=>(mem_sdiff.mp (mem_sdiff.mp h).1).1
  have Qa (z : V) (zq : z∈Q) : ∃ v∈A,G.Adj z v := by
    have z3 : G.dist a z=3 := by
      have l := dark_dist_ge_three hc zq
      apply Classical.byContradiction
      intro e
      have bad := distanceTwo_add_two_le_even_of_far hc (show 4≤G.dist a z by omega)
      have h := even a
      omega
    exact (mem_filter.mp ((firstDark_iff_distance_three hc zq).mpr z3)).2
  have visibleHit (u : V) (ua : u∈A) : ∃ p∈P,G.Adj u p := by
    obtain ⟨uc,up⟩ := mem_sdiff.mp (visible_in_nonports allC ua)
    obtain ⟨p,pp,pu⟩ := (nonport_mem_second_iff_neighbor_port hc uc up (.inl rfl)).mp ua
    obtain ⟨pc,ap⟩ := mem_filter.mp pp
    exact ⟨p,mem_filter.mpr ⟨pc,.inl ap⟩,pu⟩
  have hitTwo {p v z : V} (pp : p∈P) (pa : G.Adj p v) (vz : G.Adj v z) (zq : z∈Q) :
      z∈DistanceTwo G p := by
    obtain ⟨zf,noA⟩ := mem_sdiff.mp zq
    obtain ⟨zc,zp⟩ := mem_sdiff.mp zf
    have ne : p≠z := fun e=>zp (e ▸ pp)
    have no : ¬G.Adj p z := fun e=>noA
      ((nonport_mem_second_iff_neighbor_port hc zc zp (.inl rfl)).mpr
        ⟨p,mem_filter.mpr ⟨(mem_filter.mp pp).1,allC p pp⟩,e.symm⟩)
    exact d2 hc ne no pa vz
  obtain ⟨p,q,pq,pe⟩ := card_eq_two.mp C2
  have pP : p∈P := by simp [P,pe]
  have qP : q∈P := by simp [P,pe]
  let X := Q∩DistanceTwo G p
  let Y := Q∩DistanceTwo G q
  have qBound (u : V) (up : u∈P) : (Q∩DistanceTwo G u).card≤2 := by
    have dis : Disjoint (Q∩DistanceTwo G u) (cutPorts D) :=
      (shore_disjoint cd).mono (inter_subset_left.trans Qc) (filter_subset _ _)
    have sub := union_subset (show Q∩DistanceTwo G u⊆DistanceTwo G u from inter_subset_right)
      (cross_ports_at_distance_two hc cd (mem_filter.mp up).1 (allC u up) allD)
    have h := (card_le_card sub).trans (distanceTwo_le_of_even 5 u (even u))
    rw [card_union_of_disjoint dis,D3] at h
    omega
  have x2 : X.card≤2 := qBound p pP
  have y2 : Y.card≤2 := qBound q qP
  have xy : X∪Y=Q := by
    apply Subset.antisymm (union_subset inter_subset_left inter_subset_left)
    intro z zq
    obtain ⟨v,va,zv⟩ := Qa z zq
    obtain ⟨u,up,vu⟩ := visibleHit v va
    have upq : u=p ∨ u=q := by simpa [P,pe] using up
    rcases upq with e|e
    · exact mem_union_left _ (mem_inter.mpr ⟨zq,hitTwo pP (e ▸ vu.symm) zv.symm zq⟩)
    exact mem_union_right _ (mem_inter.mpr ⟨zq,hitTwo qP (e ▸ vu.symm) zv.symm zq⟩)
  have q4 : Q.card≤4 := by
    have h := card_union_le X Y
    rw [xy] at h
    omega
  have qHit (z : V) (zq : z∈Q) : 6≤Q.card+(A.filter (G.Adj z)).card := by
    have sub : G.neighborFinset z⊆(Q.erase z)∪(A.filter (G.Adj z)) := by
      intro u um
      have zu := (mem_neighborFinset G z u).mp um
      by_cases uq : u∈Q
      · exact mem_union_left _ (mem_erase.mpr ⟨zu.ne.symm,uq⟩)
      exact mem_union_right _ (mem_filter.mpr ⟨dark_boundary_is_visible hc allC zq zu uq,zu⟩)
    have h := (card_le_card sub).trans (card_union_le (Q.erase z) (A.filter (G.Adj z)))
    rw [card_neighborFinset_eq_degree,card_erase_of_mem zq] at h
    have zHigh := high z (Qc zq)
    have pos := card_pos.mpr ⟨z,zq⟩
    omega
  obtain ⟨z,zq⟩ := qpos
  have h := qHit z zq
  have lim : (A.filter (G.Adj z)).card≤A.card := card_le_card (filter_subset _ _)
  have q3 : 3≤Q.card := by omega
  by_cases size : Q.card=3
  · obtain ⟨u,ua⟩ := card_pos.mp (show 0<A.card by omega)
    obtain ⟨v,vP,uv⟩ := visibleHit u ua
    have big : Q⊆Q∩DistanceTwo G v := by
      intro w wq
      have card := qHit w wq
      have eq : A.filter (G.Adj w)=A := eq_of_subset_of_card_le (filter_subset _ _) (by omega)
      have wu : G.Adj w u := (mem_filter.mp (eq.symm ▸ ua)).2
      exact mem_inter.mpr ⟨wq,hitTwo vP uv.symm wu.symm wq⟩
    have l := card_le_card big
    have u := qBound v vP
    omega
  have qeq : Q.card=4 := by omega
  have sum := card_union_add_card_inter X Y
  rw [xy,qeq] at sum
  have xCard : X.card=2 := by omega
  have yCard : Y.card=2 := by omega
  have diss : Disjoint X Y := by
    rw [disjoint_iff_inter_eq_empty]
    exact card_eq_zero.mp (by omega)
  let U := A.filter (G.Adj p)
  let V' := A.filter (G.Adj q)
  have u2 : 2≤U.card := by
    obtain ⟨z,zx⟩ := card_pos.mp (show 0<X.card by omega)
    have zq := (mem_inter.mp zx).1
    have zhit := qHit z zq
    have sub : A.filter (G.Adj z)⊆U := by
      intro v vh
      obtain ⟨va,zv⟩ := mem_filter.mp vh
      obtain ⟨u,uP,vu⟩ := visibleHit v va
      have last : u=p ∨ u=q := by simpa [P,pe] using uP
      rcases last with e|e
      · exact mem_filter.mpr ⟨va,e ▸ vu.symm⟩
      have zy : z∈Y := mem_inter.mpr ⟨zq,hitTwo qP (e ▸ vu.symm) zv.symm zq⟩
      exact (disjoint_left.mp diss zx zy).elim
    have c := card_le_card sub
    omega
  have v2 : 2≤V'.card := by
    obtain ⟨z,zy⟩ := card_pos.mp (show 0<Y.card by omega)
    have zq := (mem_inter.mp zy).1
    have zhit := qHit z zq
    have sub : A.filter (G.Adj z)⊆V' := by
      intro v vh
      obtain ⟨va,zv⟩ := mem_filter.mp vh
      obtain ⟨u,uP,vu⟩ := visibleHit v va
      have last : u=p ∨ u=q := by simpa [P,pe] using uP
      rcases last with e|e
      · have zx : z∈X := mem_inter.mpr ⟨zq,hitTwo pP (e ▸ vu.symm) zv.symm zq⟩
        exact (disjoint_left.mp diss zx zy).elim
      exact mem_filter.mpr ⟨va,e ▸ vu.symm⟩
    have c := card_le_card sub
    omega
  have visDark (v : V) (va : v∈A) : ∃ z∈Q,G.Adj v z := by
    apply Classical.byContradiction
    intro no
    obtain ⟨vc,vp⟩ := mem_sdiff.mp (visible_in_nonports allC va)
    have sub : G.neighborFinset v⊆P∪A.erase v := by
      intro u hu
      have vu := (mem_neighborFinset G v u).mp hu
      have uc := mem_of_mem_erase (nonport_neighbors_subset vc vp hu)
      by_cases up : u∈P
      · exact mem_union_left _ up
      have ua : u∈A := Classical.byContradiction (fun n=>no ⟨u,mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨uc,up⟩,n⟩,vu⟩)
      exact mem_union_right _ (mem_erase.mpr ⟨vu.ne.symm,ua⟩)
    have c := (card_le_card sub).trans (card_union_le P (A.erase v))
    rw [card_neighborFinset_eq_degree,card_erase_of_mem va] at c
    have p2 : P.card=2 := C2
    have vh := high v vc
    omega
  have ap : U∪V'⊆A := union_subset (filter_subset _ _) (filter_subset _ _)
  have dis : Disjoint U V' := by
    apply disjoint_left.mpr
    intro v u w
    obtain ⟨va,pv⟩ := mem_filter.mp u
    obtain ⟨_,qv⟩ := mem_filter.mp w
    obtain ⟨z,zq,vz⟩ := visDark v va
    exact disjoint_left.mp diss (mem_inter.mpr ⟨zq,hitTwo pP pv vz zq⟩)
      (mem_inter.mpr ⟨zq,hitTwo qP qv vz zq⟩)
  have final := card_le_card ap
  rw [card_union_of_disjoint dis] at final
  omega

#print axioms no_three_visible_on_two_port_shore
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
