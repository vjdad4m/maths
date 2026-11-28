import DegreeFiveThreeThreeUniversalShape189







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

private theorem dark_cover_by_three
    (Q U V' W : Finset V) (eq : U∪V'∪W=Q)
    (u2 : U.card≤2) (v2 : V'.card≤2) (w2 : W.card≤2)
    (atleast : 3≤Q.card)
    (q3_all : Q.card=3 → U=Q)
    (q4_pair : Q.card=4 → U∪V'=Q ∧ U∪W=Q ∧ V'∪W=Q) :
    5≤Q.card ∧ Q.card≤6 := by
  have c := card_union_le U V'
  have d := card_union_le (U∪V') W
  rw [eq] at d
  refine ⟨?_,by omega⟩
  apply Classical.byContradiction
  intro no
  by_cases is3 : Q.card=3
  · rw [q3_all is3,is3] at u2
    omega
  have q4 : Q.card=4 := by omega
  obtain ⟨a,b,c'⟩ := q4_pair q4
  have dis (X Y : Finset V) (x2 : X.card≤2) (y2 : Y.card≤2) (h : X∪Y=Q) : Disjoint X Y := by
    have a := card_union_add_card_inter X Y
    rw [h,q4] at a
    rw [disjoint_iff_inter_eq_empty]
    exact card_eq_zero.mp (by omega)
  have uv := dis U V' u2 v2 a
  have uw := dis U W u2 w2 b
  have vw := dis V' W v2 w2 c'
  have all := congrArg Finset.card eq
  rw [card_union_of_disjoint (disjoint_union_left.mpr ⟨uw,vw⟩),card_union_of_disjoint uv] at all
  rw [a,q4] at c
  have alt := card_union_le U W
  rw [b,q4] at alt
  omega

/-- Distance-two head geometry for the universal-cut (3,3) case:
the dark shore is empty or order five or six, and no porter can
meet two visible vertices in the nonempty case. -/
theorem three_visible_dark_orders_and_port_limit
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (D3 : (cutPorts D).card=3)
    (allC : ∀ z∈cutPorts C,G.Adj a z) (allD : ∀ z∈cutPorts D,G.Adj a z)
    (Dpos : 1≤(secondShore D a).card) (A3 : (secondShore C a).card=3)
    (high : ∀ z∈Shore C,5≤G.degree z) (positive : (dark C).Nonempty) :
    5≤(dark C).card ∧ (dark C).card≤6 ∧
      ∀ p∈cutPorts C,∀ x∈secondShore C a,∀ y∈secondShore C a,
        G.Adj p x → G.Adj p y → x=y := by
  classical
  let A := secondShore C a
  let Q := dark C
  let P := cutPorts C
  let S (x : V) := Q.filter (G.Adj x)
  have a3 : A.card=3 := A3
  have qNonempty : Q.Nonempty := positive
  have tally := distance_two_at_cut_lower two cd
  have cap := distanceTwo_le_of_even 5 a (even a)
  have d2full : (DistanceTwo G a).card=5 := by omega
  have Qc : Q⊆Shore C := fun _ h=>(mem_sdiff.mp (mem_sdiff.mp h).1).1
  have Qa (z : V) (zq : z∈Q) : ∃ u∈A,G.Adj z u := by
    have l := dark_dist_ge_three hc zq
    have z3 : G.dist a z=3 := by
      apply Classical.byContradiction
      intro e
      have h := distanceTwo_add_two_le_even_of_far hc (show 4≤G.dist a z by omega)
      have k := even a
      omega
    exact (mem_filter.mp ((firstDark_iff_distance_three hc zq).mpr z3)).2
  have visibleHit (x : V) (xA : x∈A) : ∃ p∈P,G.Adj p x := by
    obtain ⟨xc,xp⟩ := mem_sdiff.mp (visible_in_nonports allC xA)
    obtain ⟨p,pa,xp⟩ := (nonport_mem_second_iff_neighbor_port hc xc xp (.inl rfl)).mp xA
    obtain ⟨pc,ap⟩ := mem_filter.mp pa
    exact ⟨p,mem_filter.mpr ⟨pc,.inl ap⟩,xp.symm⟩
  have charge {p v z : V} (pp : p∈P) (pv : G.Adj p v) (zv : G.Adj z v) (zq : z∈Q) :
      z∈DistanceTwo G p := by
    obtain ⟨zf,za⟩ := mem_sdiff.mp zq
    obtain ⟨zc,zp⟩ := mem_sdiff.mp zf
    have ne : p≠z := fun e=>zp (e ▸ pp)
    have no : ¬G.Adj p z := fun h=>za ((nonport_mem_second_iff_neighbor_port hc zc zp (.inl rfl)).mpr
      ⟨p,mem_filter.mpr ⟨(mem_filter.mp pp).1,allC p pp⟩,h.symm⟩)
    exact d2 hc ne no pv zv.symm
  have shell (p : V) (pp : p∈P) {K : Finset V} (KQ : K⊆Q) (KP : K⊆DistanceTwo G p) :
      K.card≤2 := by
    have dis : Disjoint K (cutPorts D) := (shore_disjoint cd).mono (KQ.trans Qc) (filter_subset _ _)
    have e := cross_ports_at_distance_two hc cd (mem_filter.mp pp).1 (allC p pp) allD
    have k := (card_le_card (union_subset KP e)).trans (distanceTwo_le_of_even 5 p (even p))
    rw [card_union_of_disjoint dis,D3] at k
    omega
  have single (u : V) (ua : u∈A) : (S u).card≤2 := by
    obtain ⟨p,pp,pu⟩ := visibleHit u ua
    apply shell p pp (show S u⊆Q from filter_subset _ _)
    intro z hz
    obtain ⟨zq,uz⟩ := mem_filter.mp hz
    exact charge pp pu uz.symm zq
  have pair (u v : V) (ua : u∈A) (va : v∈A) (uv : u≠v) :
      ∃ w∈A,w≠u ∧ w≠v ∧ A={u,v,w} := by
    have sub : ({u,v} : Finset V)⊆A := insert_subset_iff.mpr ⟨ua,singleton_subset_iff.mpr va⟩
    have two : ({u,v} : Finset V).card=2 := by simp [uv]
    have tally := card_sdiff_add_card_eq_card sub
    obtain ⟨w,ww⟩ := card_pos.mp (show 0<(A\({u,v} : Finset V)).card by omega)
    obtain ⟨wa,wn⟩ := mem_sdiff.mp ww
    have wu : w≠u := fun e=>wn (by simp [e])
    have wv : w≠v := fun e=>wn (by simp [e])
    have c : ({u,v,w} : Finset V).card=3 := by simp [uv,wu.symm,wv.symm]
    have d : ({u,v,w} : Finset V)⊆A := insert_subset_iff.mpr
      ⟨ua,insert_subset_iff.mpr ⟨va,singleton_subset_iff.mpr wa⟩⟩
    exact ⟨w,wa,wu,wv,(eq_of_subset_of_card_le d (by omega)).symm⟩
  have cover3 {u v w : V} (eq : A={u,v,w}) : S u∪S v∪S w=Q := by
    apply Subset.antisymm (union_subset (union_subset (filter_subset _ _) (filter_subset _ _)) (filter_subset _ _))
    intro z zq
    obtain ⟨x,xA,zx⟩ := Qa z zq
    have cases' : x=u ∨ x=v ∨ x=w := by simpa [eq] using xA
    rcases cases' with h|h|h
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨zq,h ▸ zx.symm⟩))
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨zq,h ▸ zx.symm⟩))
    exact mem_union_right _ (mem_filter.mpr ⟨zq,h ▸ zx.symm⟩)
  have darkDeg (z : V) (zq : z∈Q) : 6≤Q.card+(A.filter (G.Adj z)).card := by
    have sub : G.neighborFinset z⊆(Q.erase z)∪(A.filter (G.Adj z)) := by
      intro w wm
      have zw := (mem_neighborFinset G z w).mp wm
      by_cases wq : w∈Q
      · exact mem_union_left _ (mem_erase.mpr ⟨zw.ne.symm,wq⟩)
      exact mem_union_right _ (mem_filter.mpr ⟨dark_boundary_is_visible hc allC zq zw wq,zw⟩)
    have hd := high z (Qc zq)
    have h := (card_le_card sub).trans (card_union_le (Q.erase z) (A.filter (G.Adj z)))
    rw [card_neighborFinset_eq_degree,card_erase_of_mem zq] at h
    have p := card_pos.mpr ⟨z,zq⟩
    omega
  obtain ⟨z,zq⟩ := qNonempty
  have basic := darkDeg z zq
  have q3 : 3≤Q.card := by
    have q := card_le_card (show A.filter (G.Adj z)⊆A from filter_subset _ _)
    omega
  obtain ⟨x,xA,y,yA,xy⟩ := one_lt_card.mp (show 1<A.card by omega)
  obtain ⟨w,wA,wx,wy,all⟩ := pair x y xA yA xy
  have full3 (size : Q.card=3) : S x=Q := by
    apply Subset.antisymm (filter_subset _ _)
    intro v vq
    have h := darkDeg v vq
    have eq : A.filter (G.Adj v)=A := eq_of_subset_of_card_le (filter_subset _ _) (by omega)
    have vr : v∈S x := mem_filter.mpr ⟨vq,(mem_filter.mp (eq.symm ▸ xA)).2.symm⟩
    exact vr
  have full4 (size : Q.card=4) (u v : V) (uA : u∈A) (vA : v∈A) (uv : u≠v) :
      S u∪S v=Q := by
    apply Subset.antisymm (union_subset (filter_subset _ _) (filter_subset _ _))
    intro z zq
    have n := darkDeg z zq
    apply Classical.byContradiction
    intro no
    have p : A.filter (G.Adj z)⊆(A.erase u).erase v := by
      intro s hs
      obtain ⟨sa,zs⟩ := mem_filter.mp hs
      apply mem_erase.mpr
      refine ⟨?_,mem_erase.mpr ⟨?_,sa⟩⟩
      · intro h
        exact no (mem_union_right _ (mem_filter.mpr ⟨zq,(h ▸ zs).symm⟩))
      intro h
      exact no (mem_union_left _ (mem_filter.mpr ⟨zq,(h ▸ zs).symm⟩))
    have m := card_le_card p
    rw [card_erase_of_mem (mem_erase.mpr ⟨uv.symm,vA⟩),card_erase_of_mem uA,a3] at m
    omega
  have bounds := dark_cover_by_three Q (S x) (S y) (S w) (cover3 all)
    (single x xA) (single y yA) (single w wA) q3 full3
    (fun h=>⟨full4 h x y xA yA xy,full4 h x w xA wA wx.symm,full4 h y w yA wA wy.symm⟩)
  refine ⟨bounds.1,bounds.2,?_⟩
  intro p pp u uA v vA pu pv
  apply Classical.byContradiction
  intro uv
  obtain ⟨w,wA,_,_,tot⟩ := pair u v uA vA uv
  have QP : S u∪S v⊆DistanceTwo G p := by
    intro z zq
    rcases mem_union.mp zq with h|h
    · obtain ⟨zq,uz⟩ := mem_filter.mp h
      exact charge pp pu uz.symm zq
    obtain ⟨zq,vz⟩ := mem_filter.mp h
    exact charge pp pv vz.symm zq
  have bound := shell p pp (show S u∪S v⊆Q from union_subset (filter_subset _ _) (filter_subset _ _)) QP
  have c := card_union_le (S u∪S v) (S w)
  rw [cover3 tot] at c
  have w2 := single w wA
  omega

#print axioms three_visible_dark_orders_and_port_limit
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
