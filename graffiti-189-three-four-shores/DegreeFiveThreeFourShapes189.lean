import DegreeFiveFourForeignTight189
import DegreeFiveOppNonportFour189


namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset
open private Shore shore_off shore_closed shore_disjoint from DegreeFiveActualCut189
open private Cmp from DegreeFiveThreeForeignImpossible189
open private nonport_degree_bound_small nonport_neighbors_subset from DegreeFiveThreeFiveShapes189
open private four_foreign_double_charge_inputs from DegreeFiveTwoFourShapes189
open ArticulationPair
open private secondShore four_in_nonsingleton from DegreeFiveDistanceTwoThreeClose189
open private d2 from CrossSaturation189
open private sharedPortSet inside_high_at_least_three from DegreeFiveBalancedCommonRoot189
open private shores_add_two_le_graph_order from DegreeFiveBothFourFiveFifteenClose189
open private graph_order_le_shores_add_two from DegreeFiveBothNonsaturated189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

theorem three_four_shore_cardinality_cases
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    (C3 : (cutPorts C).card=3) (D4 : (cutPorts D).card=4)
    {x : V} (xc : x∈Shore C) (ax : G.Adj a x) (bx : G.Adj b x) :
    ((Shore C).card=4 ∧ (Shore D).card≤8 ∧ ∀ w∈Shore D,5≤G.degree w) ∨
    ((Shore C).card=6 ∧ ((Shore D).card≤7 ∨ ((Shore D).card≤8 ∧ ∀ w∈Shore D,5≤G.degree w))) ∨
    ((Shore C).card=7 ∧ ((Shore D).card=4 ∨ ∀ z∈Shore C,¬5≤G.degree z → z∉cutPorts C) ∧
      (Shore D).card≤6) ∨ ((Shore C).card=8 ∧ (Shore D).card=4) := by
  classical
  have ab : a≠b := by intro e; rw [e,dist_self] at two; omega
  have c4 : 4≤(Shore C).card := by
    apply four_in_nonsingleton degree
    have h : (cutPorts C).card≤(Shore C).card := card_le_card (filter_subset _ _)
    omega
  have d4 : 4≤(Shore D).card := by
    have h : (cutPorts D).card≤(Shore D).card := card_le_card (filter_subset _ _)
    omega
  let E := Shore C \ cutPorts C
  have eCount : E.card+3=(Shore C).card := by
    have h : E.card+(cutPorts C).card=(Shore C).card :=
      card_sdiff_add_card_eq_card (filter_subset _ _)
    rwa [C3] at h
  have low (z : V) (ze : z∈E) (small : (Shore C).card≤5) : ¬5≤G.degree z := by
    obtain ⟨zc,zn⟩ := mem_sdiff.mp ze
    have m := nonport_degree_bound_small zc zn
    omega
  have cNot5 : (Shore C).card≠5 := by
    intro n
    obtain ⟨u,ue,v,ve,uv⟩ := one_lt_card.mp (show 1<E.card by omega)
    exact (degree u v uv).elim (low u ue (by omega)) (low v ve (by omega))
  by_cases small : (Shore C).card=4
  · obtain ⟨z,ze⟩ := card_pos.mp (show 0<E.card by omega)
    have zlow := low z ze (by omega)
    obtain ⟨zc,zn⟩ := mem_sdiff.mp ze
    have za : ¬G.Adj a z := fun h=>zn (mem_filter.mpr ⟨zc,.inl h⟩)
    have zb : ¬G.Adj b z := fun h=>zn (mem_filter.mpr ⟨zc,.inr h⟩)
    have xz : G.Adj x z := by
      have xNe : x≠z := fun e=>za (e ▸ ax)
      have xHigh := (degree x z xNe).resolve_right zlow
      have lowB : 3≤(inside G (Shore C) x).card := inside_high_at_least_three xc xHigh
      have iSub : inside G (Shore C) x⊆(Shore C).erase x := by
        intro w wm
        obtain ⟨wc,xw⟩ := mem_filter.mp wm
        exact mem_erase.mpr ⟨xw.ne.symm,wc⟩
      have eq : inside G (Shore C) x=(Shore C).erase x := eq_of_subset_of_card_le iSub (by
        rw [card_erase_of_mem xc,small]
        omega)
      have zIn : z∈inside G (Shore C) x := by rw [eq]; exact mem_erase.mpr ⟨xNe.symm,zc⟩
      exact (mem_filter.mp zIn).2
    let F := Shore D \ cutPorts D
    let B := F.filter (fun u=>G.dist x u≠4)
    have fN : F.card+4=(Shore D).card := by
      have h : F.card+(cutPorts D).card=(Shore D).card :=
        card_sdiff_add_card_eq_card (filter_subset _ _)
      rwa [D4] at h
    have budgets := four_foreign_double_charge_inputs hc two even conn cd cover D4 xc ax bx
    have f1 : F.card≤B.card+1 := budgets.2.2.1
    have xEcc := (four_foreign_near_with_exception hc two even conn cd cover D4 xc ax bx).2.1
    have za2 := d2 hc (show z≠a from fun e=>(shore_off C).1 (e ▸ zc)) (fun e=>za e.symm) xz.symm ax.symm
    have zb2 := d2 hc (show z≠b from fun e=>(shore_off C).2 (e ▸ zc)) (fun e=>zb e.symm) xz.symm bx.symm
    have noF : Disjoint ({z,a,b} : Finset V) B := by
      refine disjoint_left.mpr ?_
      intro u uh uf
      have ud := (mem_sdiff.mp (mem_filter.mp uf).1).1
      simp only [mem_insert,mem_singleton] at uh
      rcases uh with rfl|rfl|rfl
      · exact disjoint_left.mp (shore_disjoint cd) zc ud
      · exact (shore_off D).1 ud
      exact (shore_off D).2 ud
    have subset : ({z,a,b} : Finset V)∪B ⊆ EvenFrom G z := by
      intro u hu
      rcases mem_union.mp hu with h|h
      · simp only [mem_insert,mem_singleton] at h
        apply mem_filter.mpr
        refine ⟨mem_univ _,?_⟩
        rcases h with h|h|h
        · rw [h,dist_self]
          decide
        · have hh : G.dist z a=2 := by simpa [DistanceTwo] using za2
          rw [h,hh]
          decide
        have hh : G.dist z b=2 := by simpa [DistanceTwo] using zb2
        rw [h,hh]
        decide
      obtain ⟨uf,no4⟩ := mem_filter.mp h
      obtain ⟨ud,un⟩ := mem_sdiff.mp uf
      have lower := opposite_nonporters_dist_at_least_four hc cd zc ud zn un
      have ecc := xEcc u
      have tri := hc.dist_triangle (u:=z) (v:=x) (w:=u)
      have edge := dist_eq_one_iff_adj.mpr xz.symm
      have eq : G.dist z u=4 := by omega
      exact mem_filter.mpr ⟨mem_univ _,by rw [eq]; decide⟩
    have count : ({z,a,b} : Finset V).card=3 := by
      have zne : z∉({a,b} : Finset V) := by
        simp [show z≠a from fun e=>(shore_off C).1 (e ▸ zc),
          show z≠b from fun e=>(shore_off C).2 (e ▸ zc)]
      rw [card_insert_of_not_mem zne]
      simp [ab]
    refine .inl ⟨small,?_,?_⟩
    · have cap := (card_le_card subset).trans (even z)
      rw [card_union_of_disjoint noF,count] at cap
      omega
    intro w wd
    exact (degree z w (fun e=>disjoint_left.mp (shore_disjoint cd) zc (e.symm ▸ wd))).resolve_left zlow
  let F := Shore D \ cutPorts D
  let A := E.filter (G.Adj x)
  let B := F.filter (fun u=>G.dist x u≠4)
  have fN : F.card+4=(Shore D).card := by
    have h : F.card+(cutPorts D).card=(Shore D).card :=
      card_sdiff_add_card_eq_card (filter_subset _ _)
    rwa [D4] at h
  have quantities : A.card≤4 ∧ E.card≤A.card+1 ∧ F.card≤B.card+1 ∧ 2*A.card+B.card≤8 ∧
      (A.card<E.card → B=F) ∧ (A.card=4 → (Shore D).card=4) :=
    four_foreign_double_charge_inputs hc two even conn cd cover D4 xc ax bx
  obtain ⟨a4,ca,fb,cap,sat,full⟩ := quantities
  have aSub : A⊆E := filter_subset _ _
  have ac := card_le_card aSub
  have noPortOfTight (ah : A.card<E.card) (tight : 2*A.card+B.card=8) :
      ∃ z∈Shore C,z∉cutPorts C ∧ ¬5≤G.degree z := by
    have h := card_sdiff_add_card_eq_card aSub
    obtain ⟨z,ze⟩ := card_pos.mp (show 0<(E\A).card by omega)
    obtain ⟨ze,za⟩ := mem_sdiff.mp ze
    obtain ⟨zc,zp⟩ := mem_sdiff.mp ze
    have p := tight_four_foreign_charges_exclude_port_neighbors hc two even conn cd cover D4 xc ax bx
    have sub : G.neighborFinset z⊆E.erase z := by
      intro w wm
      obtain ⟨wz,wc⟩ := mem_erase.mp (nonport_neighbors_subset zc zp wm)
      have adj := (mem_neighborFinset G z w).mp wm
      exact mem_erase.mpr ⟨wz,mem_sdiff.mpr ⟨wc,fun wp=>p tight z ze za w wp adj⟩⟩
    have tally := card_le_card sub
    rw [card_neighborFinset_eq_degree,card_erase_of_mem ze] at tally
    exact ⟨z,zc,zp,by omega⟩
  by_cases c6 : (Shore C).card=6
  · apply Or.inr; apply Or.inl
    refine ⟨c6,?_⟩
    by_cases h : (Shore D).card≤7
    · exact .inl h
    have a2 : A.card=2 := by omega
    have bf : B=F := sat (by omega)
    have eq := congrArg Finset.card bf
    obtain ⟨z,zc,zp,zlow⟩ := noPortOfTight (by omega) (by omega)
    exact .inr ⟨by omega,fun w wd=>(degree z w
      (fun e=>disjoint_left.mp (shore_disjoint cd) zc (e.symm ▸ wd))).resolve_left zlow⟩
  by_cases c7 : (Shore C).card=7
  · apply Or.inr; apply Or.inr; apply Or.inl
    refine ⟨c7,?_,?_⟩
    · by_cases dEq4 : (Shore D).card=4
      · exact .inl dEq4
      by_cases d5 : (Shore D).card=5
      · have fpos : 0<F.card := by omega
        obtain ⟨w,wF⟩ := card_pos.mp fpos
        obtain ⟨wd,wp⟩ := mem_sdiff.mp wF
        have dw := nonport_degree_bound_small wd wp
        apply Or.inr
        intro z zc zh
        have wh := (degree z w (fun e=>disjoint_left.mp (shore_disjoint cd) zc (e.symm ▸ wd))).resolve_left zh
        omega
      have a3 : A.card=3 := by
        by_contra! h
        exact dEq4 (full (by omega))
      have bf : B=F := sat (by omega)
      have eq := congrArg Finset.card bf
      obtain ⟨w,wc,wp,wh⟩ := noPortOfTight (by omega) (by omega)
      exact .inr (fun z zc zh t=>by
        have h : z≠w := fun e=>wp (e ▸ t)
        exact (degree z w h).elim zh wh)
    by_cases aEq4 : A.card=4
    · rw [full aEq4]; decide
    have bf : B=F := sat (by omega)
    have eq := congrArg Finset.card bf
    omega
  exact .inr (.inr (.inr ⟨by omega,full (by omega)⟩))

#print axioms three_four_shore_cardinality_cases
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
