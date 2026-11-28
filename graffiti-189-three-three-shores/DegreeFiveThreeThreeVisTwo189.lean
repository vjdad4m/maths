import DegreeFiveTwoThreeClose189





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

theorem no_both_visible_neighbors_at_two_visible
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (D3 : (cutPorts D).card=3)
    (allC : ∀ z∈cutPorts C,G.Adj a z) (allD : ∀ z∈cutPorts D,G.Adj a z)
    (Dpos : 1≤(secondShore D a).card) (Q2 : 2≤(dark C).card)
    (A2 : (secondShore C a).card=2)
    {p : V} (pp : p∈cutPorts C)
    (touch : ∀ x∈secondShore C a,G.Adj p x) :
    False := by
  classical
  let Q := dark C
  let W := firstDark C
  let A := secondShore C a
  let Z := univ.filter (fun z=>G.dist a z=4)
  have A2' : A.card=2 := A2
  have Wsub : W⊆Q := filter_subset _ _
  have pc := (mem_filter.mp pp).1
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

/-- If one cut touches every port, an all-high three-port shore
cannot have just two distance-two nonporters. -/
theorem no_two_visible_on_all_high_three_port_shore
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (C3 : (cutPorts C).card=3) (D3 : (cutPorts D).card=3)
    (allC : ∀ z∈cutPorts C,G.Adj a z) (allD : ∀ z∈cutPorts D,G.Adj a z)
    (Dpos : 1≤(secondShore D a).card)
    (A2 : (secondShore C a).card=2)
    (high : ∀ z∈Shore C,5≤G.degree z) : False := by
  classical
  let Q := dark C
  let A := secondShore C a
  let P := cutPorts C
  have p3 : P.card=3 := C3
  have a2 : A.card=2 := A2
  have q2 : 2≤Q.card := by
    have all : Q.card+A.card+P.card=(Shore C).card := by
      have x := card_sdiff_add_card_eq_card (visible_in_nonports allC)
      have y := card_sdiff_add_card_eq_card (show P⊆Shore C from filter_subset _ _)
      change Q.card+A.card=(Shore C\P).card at x
      omega
    obtain ⟨x,xa⟩ := card_pos.mp (show 0<A.card by omega)
    obtain ⟨xc,xp⟩ := mem_sdiff.mp (visible_in_nonports allC xa)
    have q := nonport_degree_bound_small xc xp
    have h := high x xc
    have qPos : 0<Q.card := by omega
    obtain ⟨y,yq⟩ := card_pos.mp qPos
    have sub : G.neighborFinset y⊆(Q.erase y)∪A := by
      intro w wm
      have yw := (mem_neighborFinset G y w).mp wm
      by_cases wq : w∈Q
      · exact mem_union_left _ (mem_erase.mpr ⟨yw.ne.symm,wq⟩)
      exact mem_union_right _ (dark_boundary_is_visible hc allC yq yw wq)
    have cap := (card_le_card sub).trans (card_union_le (Q.erase y) A)
    rw [card_neighborFinset_eq_degree,card_erase_of_mem yq] at cap
    have yh := high y (mem_sdiff.mp (mem_sdiff.mp yq).1).1
    omega
  have noBoth (p : V) (pp : p∈P) : ¬∀ x∈A,G.Adj p x := by
    intro hit
    exact no_both_visible_neighbors_at_two_visible hc two even conn degree cd D3 allC allD Dpos q2 A2 pp hit
  obtain ⟨u,v,uv,eq⟩ := card_eq_two.mp a2
  have uA : u∈A := by simp [eq]
  have vA : v∈A := by simp [eq]
  have visBound (x : V) (xA : x∈A) : (Q.filter (G.Adj x)).card≤2 := by
    obtain ⟨xc,xp⟩ := mem_sdiff.mp (visible_in_nonports allC xA)
    obtain ⟨p,pp,xp'⟩ := (nonport_mem_second_iff_neighbor_port hc xc xp (.inl rfl)).mp xA
    have pC := (mem_filter.mp pp).1
    have ap := (mem_filter.mp pp).2
    have pP : p∈P := mem_filter.mpr ⟨pC,.inl ap⟩
    have QD : Q.filter (G.Adj x)⊆DistanceTwo G p := by
      intro z hz
      obtain ⟨zq,xz⟩ := mem_filter.mp hz
      obtain ⟨zf,za⟩ := mem_sdiff.mp zq
      obtain ⟨zc,zp⟩ := mem_sdiff.mp zf
      have no : ¬G.Adj p z := fun e=>za
        ((nonport_mem_second_iff_neighbor_port hc zc zp (.inl rfl)).mpr ⟨p,pp,e.symm⟩)
      exact d2 hc (fun e=>zp (e ▸ pP)) no xp'.symm xz
    have dis : Disjoint (Q.filter (G.Adj x)) (cutPorts D) :=
      (shore_disjoint cd).mono (fun _ h=>(mem_sdiff.mp (mem_sdiff.mp (mem_filter.mp h).1).1).1)
        (filter_subset _ _)
    have sum := (card_le_card (union_subset QD (cross_ports_at_distance_two hc cd pC ap allD))).trans
      (distanceTwo_le_of_even 5 p (even p))
    rw [card_union_of_disjoint dis,D3] at sum
    omega
  have visPorts (x : V) (xA : x∈A) : 2≤(P.filter (G.Adj x)).card := by
    obtain ⟨xc,xp⟩ := mem_sdiff.mp (visible_in_nonports allC xA)
    have highx := high x xc
    have sub : G.neighborFinset x⊆((P.filter (G.Adj x))∪A.erase x)∪(Q.filter (G.Adj x)) := by
      intro z zm
      have xz := (mem_neighborFinset G x z).mp zm
      obtain ⟨_,zc⟩ := mem_erase.mp (nonport_neighbors_subset xc xp zm)
      by_cases zp : z∈P
      · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨zp,xz⟩))
      by_cases za : z∈A
      · exact mem_union_left _ (mem_union_right _ (mem_erase.mpr ⟨xz.ne.symm,za⟩))
      exact mem_union_right _ (mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨zc,zp⟩,za⟩,xz⟩)
    have c := card_le_card sub
    rw [card_neighborFinset_eq_degree] at c
    have t := card_union_le (P.filter (G.Adj x)) (A.erase x)
    have p := card_union_le ((P.filter (G.Adj x))∪A.erase x) (Q.filter (G.Adj x))
    rw [card_erase_of_mem xA] at t
    have low := visBound x xA
    omega
  let U := P.filter (G.Adj u)
  let V' := P.filter (G.Adj v)
  have dis : Disjoint U V' := by
    apply disjoint_left.mpr
    intro p x y
    obtain ⟨pp,up⟩ := mem_filter.mp x
    obtain ⟨_,vp⟩ := mem_filter.mp y
    exact noBoth p pp (fun w wa=>by
      have h : w=u ∨ w=v := by simpa [eq] using wa
      exact h.elim (fun e=>e.symm ▸ up.symm) (fun e=>e.symm ▸ vp.symm))
  have sum := card_le_card (show U∪V'⊆P from union_subset (filter_subset _ _) (filter_subset _ _))
  rw [card_union_of_disjoint dis] at sum
  have U2 : 2≤U.card := visPorts u uA
  have V2 : 2≤V'.card := visPorts v vA
  omega

#print axioms no_both_visible_neighbors_at_two_visible
#print axioms no_two_visible_on_all_high_three_port_shore
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
