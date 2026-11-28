import DegreeFiveTwoThreeBase189
import DegreeFiveFourForeignGeom189




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

private noncomputable def firstDark (C : Cmp (G:=G) (a:=a) (b:=b)) : Finset V :=
  (dark C).filter (fun w=>∃ u∈secondShore C a,G.Adj w u)

private theorem dark_dist_ge_three (hc : G.Connected)
    {C : Cmp (G:=G) (a:=a) (b:=b)} {x : V} (xd : x∈dark C) :
    3≤G.dist a x := by
  obtain ⟨xf,xv⟩ := mem_sdiff.mp xd
  obtain ⟨xc,xp⟩ := mem_sdiff.mp xf
  have ax : a≠x := fun e=>(shore_off C).1 (Eq.mp (congrArg (fun v : V=>v∈Shore C) e.symm) xc)
  have no : ¬G.Adj a x := fun h=>xp (mem_filter.mpr ⟨xc,.inl h⟩)
  have lo := hc.one_lt_dist_of_ne_of_not_adj ax no
  have not2 : G.dist a x≠2 := fun h=>xv (mem_inter.mpr ⟨xc,by simp [DistanceTwo,h]⟩)
  omega

private theorem firstDark_iff_distance_three (hc : G.Connected)
    {C : Cmp (G:=G) (a:=a) (b:=b)} {x : V} (xd : x∈dark C) :
    x∈firstDark C ↔ G.dist a x=3 := by
  constructor
  · rintro m
    obtain ⟨_,v,vh,xv⟩ := mem_filter.mp m
    have av : G.dist a v=2 := by simpa [DistanceTwo] using (mem_inter.mp vh).2
    have vx := dist_eq_one_iff_adj.mpr xv.symm
    have tr := hc.dist_triangle (u:=a) (v:=v) (w:=x)
    have lo := dark_dist_ge_three hc xd
    omega
  intro h
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist x a
  have len : p.length=3 := by rw [hp,dist_comm,h]
  have middle {u v : V} (q : G.Walk u v) (l : q.length=3) (metric : G.dist v u=3) :
      ∃ w,G.Adj u w ∧ G.dist v w=2 := by
    cases q with
    | nil => simp at l
    | @cons u w v e q =>
      refine ⟨w,e,?_⟩
      have near := G.dist_le q.reverse
      simp only [length_reverse] at near
      have tri := hc.dist_triangle (u:=v) (v:=w) (w:=u)
      have step := dist_eq_one_iff_adj.mpr e.symm
      simp only [length_cons] at l
      omega
  obtain ⟨v,xv,va⟩ := middle p len h
  have vv : v∈secondShore C a := by
    obtain ⟨xc,xp⟩ := mem_sdiff.mp (mem_sdiff.mp xd).1
    rcases shore_closed C x xc v xv with e|e|vc
    · exact (xp (mem_filter.mpr ⟨xc,.inl (e ▸ xv.symm)⟩)).elim
    · exact (xp (mem_filter.mpr ⟨xc,.inr (e ▸ xv.symm)⟩)).elim
    exact mem_inter.mpr ⟨vc,by simp [DistanceTwo,va]⟩
  exact mem_filter.mpr ⟨xd,v,vv,xv⟩

private theorem cross_ports_at_distance_two
    (hc : G.Connected) {C D : Cmp (G:=G) (a:=a) (b:=b)}
    (cd : C≠D) {p : V} (pc : p∈Shore C) (ap : G.Adj a p)
    (all : ∀ z∈cutPorts D,G.Adj a z) :
    cutPorts D⊆DistanceTwo G p := by
  intro z zp
  have zd := (mem_filter.mp zp).1
  have ne : p≠z := fun e=>disjoint_left.mp (shore_disjoint cd) pc (e.symm ▸ zd)
  have no : ¬G.Adj p z := by
    intro h
    rcases shore_closed C p pc z h with e|e|zc
    · exact (shore_off D).1 (Eq.mp (congrArg (fun v : V=>v∈Shore D) e) zd)
    · exact (shore_off D).2 (Eq.mp (congrArg (fun v : V=>v∈Shore D) e) zd)
    exact disjoint_left.mp (shore_disjoint cd) zc zd
  exact d2 hc ne no ap.symm (all z zp)

private theorem distance_two_at_cut_lower
    (two : G.dist a b=2)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D) :
    1+(secondShore C a).card+(secondShore D a).card≤(DistanceTwo G a).card := by
  classical
  let A := secondShore C a
  let B := secondShore D a
  have dis : Disjoint A B := (shore_disjoint cd).mono inter_subset_left inter_subset_left
  have off : b∉A∪B := fun h=>(mem_union.mp h).elim
    (fun h=>(shore_off C).2 (mem_inter.mp h).1)
    (fun h=>(shore_off D).2 (mem_inter.mp h).1)
  have sub : insert b (A∪B)⊆DistanceTwo G a := by
    intro z h
    rcases mem_insert.mp h with e|h
    · simp [DistanceTwo,e,two]
    exact (mem_union.mp h).elim (fun h=>(mem_inter.mp h).2) (fun h=>(mem_inter.mp h).2)
  have lo := card_le_card sub
  rw [card_insert_of_not_mem off,card_union_of_disjoint dis] at lo
  change 1+A.card+B.card≤(DistanceTwo G a).card
  omega

private theorem high_port_sees_two_visibles
    (hc : G.Connected) {C : Cmp (G:=G) (a:=a) (b:=b)}
    (C2 : (cutPorts C).card=2) (A2 : (secondShore C a).card=2)
    (all : ∀ z∈cutPorts C,G.Adj a z) {p : V} (pp : p∈cutPorts C) (p5 : 5≤G.degree p) :
    ∀ x∈secondShore C a,G.Adj p x := by
  classical
  let T := insert a (insert b (((cutPorts C).erase p)∪secondShore C a))
  have sub : G.neighborFinset p⊆T := by
    intro v vv
    have e := (mem_neighborFinset G p v).mp vv
    rcases shore_closed C p (mem_filter.mp pp).1 v e with ha|hb|vc
    · simp [T,ha]
    · simp [T,hb]
    by_cases vP : v∈cutPorts C
    · exact mem_insert_of_mem (mem_insert_of_mem (mem_union_left _ (mem_erase.mpr ⟨e.ne.symm,vP⟩)))
    have vis : v∈secondShore C a := (nonport_mem_second_iff_neighbor_port hc vc vP (.inl rfl)).mpr
      ⟨p,mem_filter.mpr ⟨(mem_filter.mp pp).1,all p pp⟩,e.symm⟩
    exact mem_insert_of_mem (mem_insert_of_mem (mem_union_right _ vis))
  have lim := card_union_le ((cutPorts C).erase p) (secondShore C a)
  rw [card_erase_of_mem pp,C2,A2] at lim
  have t1 := card_insert_le a (insert b (((cutPorts C).erase p)∪secondShore C a))
  have t2 := card_insert_le b (((cutPorts C).erase p)∪secondShore C a)
  have eq : G.neighborFinset p=T := eq_of_subset_of_card_le sub (by
    rw [card_neighborFinset_eq_degree]
    change (insert a (insert b (((cutPorts C).erase p)∪secondShore C a))).card≤G.degree p
    omega)
  intro x xv
  have mem : x∈G.neighborFinset p := eq.symm ▸ mem_insert_of_mem (mem_insert_of_mem (mem_union_right _ xv))
  exact (mem_neighborFinset G p x).mp mem

theorem no_two_visible_on_two_port_shore
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (C2 : (cutPorts C).card=2) (D3 : (cutPorts D).card=3)
    (allC : ∀ z∈cutPorts C,G.Adj a z) (allD : ∀ z∈cutPorts D,G.Adj a z)
    (Dpos : 1≤(secondShore D a).card) (Q2 : 2≤(dark C).card)
    (A2 : (secondShore C a).card=2) :
    False := by
  classical
  let Q := dark C
  let W := firstDark C
  let A := secondShore C a
  let Z := univ.filter (fun z=>G.dist a z=4)
  have A2' : A.card=2 := A2
  have Wsub : W⊆Q := filter_subset _ _
  obtain ⟨p,pp,p5⟩ := anywhere_high_of_two degree (show 2≤(cutPorts C).card by omega)
  have pc := (mem_filter.mp pp).1
  have touch := high_port_sees_two_visibles hc C2 A2 allC pp p5
  have wp : W⊆DistanceTwo G p := by
    intro w ww
    obtain ⟨wq,u,uv,wu⟩ := mem_filter.mp ww
    obtain ⟨wf,wA⟩ := mem_sdiff.mp wq
    obtain ⟨wc,wP⟩ := mem_sdiff.mp wf
    have ne : p≠w := fun e=>wP (e ▸ pp)
    have no : ¬G.Adj p w := fun e=>wA
      ((nonport_mem_second_iff_neighbor_port hc wc wP (.inl rfl)).mpr
        ⟨p,mem_filter.mpr ⟨pc,allC p pp⟩,e.symm⟩)
    exact d2 hc ne no (touch u uv) wu.symm
  have wd : Disjoint W (cutPorts D) := (shore_disjoint cd).mono
    (fun _ h=>(mem_sdiff.mp (mem_sdiff.mp (Wsub h)).1).1) (filter_subset _ _)
  have upper := (card_le_card (union_subset wp (cross_ports_at_distance_two hc cd pc (allC p pp) allD))).trans
    (distanceTwo_le_of_even 5 p (even p))
  rw [card_union_of_disjoint wd,D3] at upper
  have W2 : 2≤W.card := by
    apply Classical.byContradiction
    intro small
    have nq : ¬Q⊆W := fun q=>by
      have t := card_le_card q
      have u : 2≤Q.card := Q2
      omega
    obtain ⟨x,xq,xw⟩ := not_subset.mp nq
    have na : a∉Q := fun h=>(shore_off C).1 (mem_sdiff.mp (mem_sdiff.mp h).1).1
    have naw : a∉W := fun h=>na (Wsub h)
    exact small (boundary_has_at_least_two conn ⟨x,xq,xw⟩ na naw (fun y yq z nz yz=>
      .inl (mem_filter.mpr ⟨yq,z,dark_boundary_is_visible hc allC yq yz nz,yz⟩)))
  obtain ⟨w,ww,w5⟩ := anywhere_high_of_two degree W2
  have wq : w∈Q := Wsub ww
  have sub : G.neighborFinset w⊆(A∪W.erase w)∪Z := by
    intro z zm
    have wz := (mem_neighborFinset G w z).mp zm
    by_cases zq : z∈Q
    · by_cases zw : z∈W
      · exact mem_union_left _ (mem_union_right _ (mem_erase.mpr ⟨wz.ne.symm,zw⟩))
      have w3 := (firstDark_iff_distance_three hc wq).mp ww
      have lo := dark_dist_ge_three hc zq
      have no : G.dist a z≠3 := fun h=>zw ((firstDark_iff_distance_three hc zq).mpr h)
      have e := dist_eq_one_iff_adj.mpr wz
      have tri := hc.dist_triangle (u:=a) (v:=w) (w:=z)
      exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _,by omega⟩)
    exact mem_union_left _ (mem_union_left _ (dark_boundary_is_visible hc allC wq wz zq))
  have b := card_le_card sub
  rw [card_neighborFinset_eq_degree] at b
  have p := card_union_le A (W.erase w)
  have q := card_union_le (A∪W.erase w) Z
  rw [card_erase_of_mem ww] at p
  have nearCount := distance_two_at_cut_lower two cd
  have cap : (DistanceTwo G a).card+Z.card≤5 := four_layer_add_distance_two_le_five even a
  omega

#print axioms no_two_visible_on_two_port_shore
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
