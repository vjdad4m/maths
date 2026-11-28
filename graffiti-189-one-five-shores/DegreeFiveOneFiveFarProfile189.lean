import DegreeFiveOneFiveGeometry189


namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset
open private Shore shore_off shore_closed shore_disjoint shore_nonempty shore_connected shore_hit_a shore_hit_b from DegreeFiveActualCut189
open private two_walk_middle from DistanceTwoCut189
open private secondShore from DegreeFiveDistanceTwoThreeClose189
open private Cmp two_shore_budget count_cut_degree_on_two_shores portColor from DegreeFiveThreeForeignImpossible189
open private four_in_nonsingleton from DegreeFiveDistanceTwoThreeClose189
open private nonport_neighbors_subset from DegreeFiveThreeFiveShapes189
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

private theorem nonport_mem_second_iff_neighbor_port
    (hc : G.Connected) {D : Cmp (G:=G) (a:=a) (b:=b)}
    {z c : V} (zd : z∈Shore D) (zp : z∉cutPorts D) (cut : c=a ∨ c=b) :
    z∈secondShore D c ↔ ∃ w∈portColor D c,G.Adj z w := by
  have no : ¬G.Adj c z := fun e=>zp (mem_filter.mpr
    ⟨zd,cut.elim (fun h=>.inl (h ▸ e)) (fun h=>.inr (h ▸ e))⟩)
  have ne : c≠z := fun e=>cut.elim
    (fun ca=>(shore_off D).1 ((ca.symm.trans e).symm ▸ zd))
    (fun cb=>(shore_off D).2 ((cb.symm.trans e).symm ▸ zd))
  constructor
  · intro h
    have eq : G.dist c z=2 := by simpa [DistanceTwo] using (mem_inter.mp h).2
    obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist c z
    obtain ⟨w,cw,wz⟩ := two_walk_middle p (hp.trans eq)
    have wd : w∈Shore D := by
      rcases shore_closed D z zd w wz.symm with e|e|h
      · exact (zp (mem_filter.mpr ⟨zd,.inl (e ▸ wz)⟩)).elim
      · exact (zp (mem_filter.mpr ⟨zd,.inr (e ▸ wz)⟩)).elim
      exact h
    exact ⟨w,mem_filter.mpr ⟨wd,cw⟩,wz.symm⟩
  rintro ⟨w,wp,zw⟩
  exact mem_inter.mpr ⟨zd,d2 hc ne no (mem_filter.mp wp).2 zw.symm⟩

/-- All finsets are in the original graph. D is the five-port shore;
e,f are the two exclusive ports, and L,R,M are the disjoint
single-color and double-color nonporter groups. -/
structure OneFiveFarProfile (D : Cmp (G:=G) (a:=a) (b:=b)) where
  e : V
  f : V
  T : Finset V
  L : Finset V
  R : Finset V
  M : Finset V
  T_card : T.card=3
  e_port : e∈cutPorts D
  f_port : f∈cutPorts D
  e_not_b : ¬G.Adj b e
  f_not_a : ¬G.Adj a f
  T_eq : T = portColor D a ∩ portColor D b
  A_eq : portColor D a=insert e T
  B_eq : portColor D b=insert f T
  L_eq : L = ((Shore D\cutPorts D)∩secondShore D a)\secondShore D b
  R_eq : R = ((Shore D\cutPorts D)∩secondShore D b)\secondShore D a
  M_eq : M = ((Shore D\cutPorts D)∩secondShore D a)∩secondShore D b
  F_eq : L∪R∪M=Shore D\cutPorts D
  LR_disjoint : Disjoint L R
  LM_disjoint : Disjoint L M
  RM_disjoint : Disjoint R M
  count : L.card+R.card+M.card=(Shore D).card-5
  a_cap : L.card+M.card≤4
  b_cap : R.card+M.card≤4
  f_excluded : L.card+M.card=4 → ∀ w∈portColor D a,¬G.Adj f w
  e_excluded : R.card+M.card=4 → ∀ w∈portColor D b,¬G.Adj e w
  left_only : ∀ z∈L, ∀ w∈cutPorts D, G.Adj z w ↔ w=e
  right_only : ∀ z∈R, ∀ w∈cutPorts D, G.Adj z w ↔ w=f

theorem one_five_far_profile
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    (one : (cutPorts C).card=1) (five : (cutPorts D).card=5)
    (big : 10≤(Shore D).card) :
    Nonempty (OneFiveFarProfile D) := by
  classical
  obtain ⟨r,ce,ar,br,high,colors⟩ := one_five_shore_shape two conn degree cd cover one five
  have rc : r∈Shore C := by simp [ce]
  let P := cutPorts D
  let A := portColor D a
  let B := portColor D b
  let F := Shore D\P
  let T := A∩B
  let AA := secondShore D a
  let BB := secondShore D b
  let W := F∩AA
  let L := W\BB
  let R := (F∩BB)\AA
  let M := W∩BB
  have ab : a≠b := by intro h; rw [h,dist_self] at two; omega
  have A4 : 4≤A.card := colors a (.inl rfl)
  have B4 : 4≤B.card := colors b (.inr rfl)
  have pu : A∪B=P := by
    ext z
    change _ ↔ z∈(Shore D).filter (fun w=>G.Adj a w ∨ G.Adj b w)
    simp [A,B,and_or_left]
  have p5 : P.card=5 := five
  have ns (c : V) (cc : c=a ∨ c=b) : ∃ u∈P,¬G.Adj c u := by
    apply Classical.byContradiction
    intro h
    have s := (one_five_opposite_order_bound hc two even conn degree cd cover one five).2
      ⟨c,cc,fun u up=>Classical.byContradiction (fun n=>h ⟨u,up,n⟩)⟩
    omega
  obtain ⟨e,eP,eb⟩ := ns b (.inr rfl)
  obtain ⟨f,fP,fa⟩ := ns a (.inl rfl)
  have eA : e∈A := mem_filter.mpr ⟨(mem_filter.mp eP).1,((mem_filter.mp eP).2).resolve_right eb⟩
  have fB : f∈B := mem_filter.mpr ⟨(mem_filter.mp fP).1,((mem_filter.mp fP).2).resolve_left fa⟩
  have en : e∉B := fun h=>eb (mem_filter.mp h).2
  have fn : f∉A := fun h=>fa (mem_filter.mp h).2
  have Aeq : A=P.erase f := by
    apply eq_of_subset_of_card_le
    · intro z za
      exact mem_erase.mpr ⟨fun e=>fn (e ▸ za),pu ▸ mem_union_left _ za⟩
    rw [card_erase_of_mem fP,p5]
    omega
  have Beq : B=P.erase e := by
    apply eq_of_subset_of_card_le
    · intro z zb
      exact mem_erase.mpr ⟨fun e=>en (e ▸ zb),pu ▸ mem_union_right _ zb⟩
    rw [card_erase_of_mem eP,p5]
    omega
  have eT : e∉T := fun h=>en (mem_inter.mp h).2
  have fT : f∉T := fun h=>fn (mem_inter.mp h).1
  have Ap : A=insert e T := by
    apply Subset.antisymm
    · intro z za
      by_cases h : z=e
      · exact mem_insert.mpr (.inl h)
      exact mem_insert.mpr (.inr (mem_inter.mpr ⟨za,Beq.symm ▸ mem_erase.mpr ⟨h,pu ▸ mem_union_left _ za⟩⟩))
    exact insert_subset_iff.mpr ⟨eA,inter_subset_left⟩
  have Bp : B=insert f T := by
    apply Subset.antisymm
    · intro z zb
      by_cases h : z=f
      · exact mem_insert.mpr (.inl h)
      exact mem_insert.mpr (.inr (mem_inter.mpr ⟨Aeq.symm ▸ mem_erase.mpr ⟨h,pu ▸ mem_union_right _ zb⟩,zb⟩))
    exact insert_subset_iff.mpr ⟨fB,inter_subset_right⟩
  have tc : T.card=3 := by
    have h := congrArg Finset.card Ap
    have q := congrArg Finset.card Aeq
    rw [card_insert_of_not_mem eT] at h
    rw [card_erase_of_mem fP,p5] at q
    omega
  have fCap : F⊆AA∪BB := by
    intro z zf
    obtain ⟨zd,zp⟩ := mem_sdiff.mp zf
    obtain ⟨w,wp,zw⟩ := (saturated_common_foreign_port_domination hc even cd five rc ar br).2 z zd zp
    have w' : w∈A∪B := pu.symm ▸ wp
    rcases mem_union.mp w' with wa|wb
    · exact mem_union_left _ ((nonport_mem_second_iff_neighbor_port hc zd zp (.inl rfl)).mpr ⟨w,wa,zw⟩)
    exact mem_union_right _ ((nonport_mem_second_iff_neighbor_port hc zd zp (.inr rfl)).mpr ⟨w,wb,zw⟩)
  have leAB (D' : Finset V) (m : D'=AA ∨ D'=BB) : D'.card≤4 := by
    rcases m with h|h
    · rw [h]
      have q := two_shore_budget cd ⟨(shore_off C).2,(shore_off D).2⟩ two even
      change (secondShore C a).card+AA.card≤4 at q
      omega
    rw [h]
    have q := two_shore_budget cd ⟨(shore_off C).1,(shore_off D).1⟩ (by rwa [dist_comm]) even
    change (secondShore C b).card+BB.card≤4 at q
    omega
  have lm : L∪M=W := by
    ext z
    by_cases h : z∈BB <;> simp [L,M,h]
  have rm : R∪M=F∩BB := by
    ext z
    by_cases h : z∈AA <;> simp [R,M,W,h, and_left_comm]
  have lmDis : Disjoint L M := disjoint_left.mpr fun _ a b=>(mem_sdiff.mp a).2 (mem_inter.mp b).2
  have rmDis : Disjoint R M := disjoint_left.mpr fun _ a b=>(mem_sdiff.mp a).2 (mem_inter.mp (mem_inter.mp b).1).2
  have lrDis : Disjoint L R := disjoint_left.mpr fun _ a b=>(mem_sdiff.mp a).2 (mem_inter.mp (mem_sdiff.mp b).1).2
  have onlyF : L∪R∪M=F := by
    ext z
    constructor
    · intro h
      rcases mem_union.mp h with h|h
      · rcases mem_union.mp h with h|h
        · exact (mem_inter.mp (mem_sdiff.mp h).1).1
        exact (mem_inter.mp (mem_sdiff.mp h).1).1
      exact (mem_inter.mp (mem_inter.mp h).1).1
    intro zf
    rcases mem_union.mp (fCap zf) with ha|hb
    · by_cases h : z∈BB
      · exact mem_union_right _ (mem_inter.mpr ⟨mem_inter.mpr ⟨zf,ha⟩,h⟩)
      exact mem_union_left _ (mem_union_left _ (mem_sdiff.mpr ⟨mem_inter.mpr ⟨zf,ha⟩,h⟩))
    by_cases h : z∈AA
    · exact mem_union_right _ (mem_inter.mpr ⟨mem_inter.mpr ⟨zf,h⟩,hb⟩)
    exact mem_union_left _ (mem_union_right _ (mem_sdiff.mpr ⟨mem_inter.mpr ⟨zf,hb⟩,h⟩))
  have lrma := congrArg Finset.card onlyF
  rw [card_union_of_disjoint (disjoint_union_left.mpr ⟨lmDis,rmDis⟩),card_union_of_disjoint lrDis] at lrma
  have fcount : F.card+P.card=(Shore D).card := card_sdiff_add_card_eq_card (filter_subset _ _)
  have aml : L.card+M.card=W.card := by rw [←lm,card_union_of_disjoint lmDis]
  have bmr : R.card+M.card=(F∩BB).card := by rw [←rm,card_union_of_disjoint rmDis]
  refine ⟨⟨e,f,T,L,R,M,tc,eP,fP,eb,fa,rfl,Ap,Bp,rfl,rfl,rfl,onlyF,lrDis,lmDis,rmDis,by omega,
    ?_,?_,?_,?_,?_,?_⟩⟩
  · exact aml.le.trans ((card_le_card inter_subset_right).trans (leAB _ (.inl rfl)))
  · exact bmr.le.trans ((card_le_card inter_subset_right).trans (leAB _ (.inr rfl)))
  · intro full w wa fw
    have fD := (mem_filter.mp fP).1
    have off : a≠f := fun e=>(shore_off D).1 (e.symm ▸ fD)
    have fa2 : f∈AA := mem_inter.mpr ⟨fD,d2 hc off fa (mem_filter.mp wa).2 fw.symm⟩
    have nf : f∉W := fun h=>(mem_sdiff.mp (mem_inter.mp h).1).2 fP
    have one := card_le_card (insert_subset_iff.mpr ⟨fa2,(show W⊆AA from inter_subset_right)⟩)
    rw [card_insert_of_not_mem nf] at one
    have cap := leAB AA (.inl rfl)
    omega
  · intro full w wb ew
    have eD := (mem_filter.mp eP).1
    have off : b≠e := fun h=>(shore_off D).2 (h.symm ▸ eD)
    have eb2 : e∈BB := mem_inter.mpr ⟨eD,d2 hc off eb (mem_filter.mp wb).2 ew.symm⟩
    have ne : e∉F∩BB := fun h=>(mem_sdiff.mp (mem_inter.mp h).1).2 eP
    have one := card_le_card (insert_subset_iff.mpr ⟨eb2,(show F∩BB⊆BB from inter_subset_right)⟩)
    rw [card_insert_of_not_mem ne] at one
    have cap := leAB BB (.inr rfl)
    omega
  · intro z zl w wp
    obtain ⟨zw,noB⟩ := mem_sdiff.mp zl
    obtain ⟨zf,za⟩ := mem_inter.mp zw
    obtain ⟨zd,zp⟩ := mem_sdiff.mp zf
    have stop (w : V) (wb : w∈B) : ¬G.Adj z w := fun e=>noB
      ((nonport_mem_second_iff_neighbor_port hc zd zp (.inr rfl)).mpr ⟨w,wb,e⟩)
    have eq (w : V) (wp : w∈P) (zw : G.Adj z w) : w=e := by
      apply Classical.byContradiction
      intro ne
      exact stop w (Beq.symm ▸ mem_erase.mpr ⟨ne,wp⟩) zw
    refine ⟨eq w wp,?_⟩
    intro wo
    obtain ⟨t,ta,zt⟩ := (nonport_mem_second_iff_neighbor_port hc zd zp (.inl rfl)).mp za
    rw [wo,←eq t (pu ▸ mem_union_left _ ta) zt]
    exact zt
  intro z zr w wp
  obtain ⟨zw,noA⟩ := mem_sdiff.mp zr
  obtain ⟨zf,zb⟩ := mem_inter.mp zw
  obtain ⟨zd,zp⟩ := mem_sdiff.mp zf
  have stop (w : V) (wa : w∈A) : ¬G.Adj z w := fun e=>noA
    ((nonport_mem_second_iff_neighbor_port hc zd zp (.inl rfl)).mpr ⟨w,wa,e⟩)
  have eq (w : V) (wp : w∈P) (zw : G.Adj z w) : w=f := by
    apply Classical.byContradiction
    intro ne
    exact stop w (Aeq.symm ▸ mem_erase.mpr ⟨ne,wp⟩) zw
  refine ⟨eq w wp,?_⟩
  intro wo
  obtain ⟨t,tb,zt⟩ := (nonport_mem_second_iff_neighbor_port hc zd zp (.inr rfl)).mp zb
  rw [wo,←eq t (pu ▸ mem_union_right _ tb) zt]
  exact zt

#print axioms one_five_far_profile
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
