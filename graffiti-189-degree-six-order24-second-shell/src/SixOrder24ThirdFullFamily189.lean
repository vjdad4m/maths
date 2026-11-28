import SixOrder24ThirdPortBounds189

namespace Graffiti189LongestPath
open SimpleGraph Finset
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

theorem cross_port_overload
    (hc : G.Connected) (cap : ∀ v,(EvenFrom G v).card≤7)
    {x c : V} (C : Finset V) (cOut : c∉C) (large : 7≤C.card)
    (no : ∀ z∈C,¬G.Adj c z)
    (largePort : ∀ z∈C,(RadiusFiveNearEquality.thirdPorts (x:=x) G c).card+
      (RadiusFiveNearEquality.thirdPorts (x:=x) G z).card>(Shell G x 4).card) : False := by
  classical
  let P (z : V) := RadiusFiveNearEquality.thirdPorts (x:=x) G z
  have sub : C⊆DistanceTwo G c := by
    intro z zm
    have s : P c∪P z⊆Shell G x 4 := union_subset (filter_subset _ _) (filter_subset _ _)
    have t := card_le_card s
    have u := card_union_add_card_inter (P c) (P z)
    have p := largePort z zm
    change (P c).card+(P z).card>(Shell G x 4).card at p
    obtain ⟨w,wm⟩ := card_pos.mp (show 0<(P c∩P z).card by omega)
    obtain ⟨wc,wz⟩ := mem_inter.mp wm
    have ne : c≠z := fun e=>cOut (e.symm ▸ zm)
    exact Graffiti189LongestPath.ThresholdSix.ThreeCut.two_of_common hc ne (no z zm)
      (mem_filter.mp wc).2 (mem_filter.mp wz).2.symm
  have l := (card_le_card sub).trans (distanceTwo_le_of_even 6 c (cap c))
  omega

namespace RadiusFiveNearEquality

theorem no_order24_full_near_family
    (hc : G.Connected) (cap : ∀ v,(EvenFrom G v).card≤7)
    (conn : ∀ S : Finset V,S.card<3→(G.induce ((↑S:Set V)ᶜ)).Connected)
    (high : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {x : V} (dx : G.degree x≤6) (n : 24≤Fintype.card V)
    (Q : RadiusFiveNearEquality G x) (none : Shell G x 5=∅)
    (c12 : (Shell G x 3).card=12)
    (shapes : ((Shell G x 1).card=6 ∧ (Shell G x 4).card=2) ∨
      ((Shell G x 1).card=5 ∧ (Shell G x 4).card=3)) : False := by
  classical
  let A := Shell G x 1
  let C := Shell G x 3
  let D := Shell G x 4
  let R := A\Q.T
  let P (a : V) := JointFarGroup G x a
  let H (a : V) := Q.foreignThird a
  let L (z : V) := thirdPorts (x:=x) G z
  have cCov : C⊆Q.T.biUnion P := fun z zc=>Q.far_cover (mem_union_left _ zc)
  have exactSize : C.card=Q.T.card*4 := by rw [Q.t3]; exact c12
  obtain ⟨full,sep⟩ := exact_cover_members Q.T P C 4 cCov exactSize Q.far_card
  have rSize : R.card+3=A.card := by
    have h := card_sdiff_add_card_eq_card (show Q.T⊆A from Q.near)
    rw [Q.t3] at h
    exact h
  have group (z : V) (zm : z∈C) : ∃ a∈Q.T,z∈P a := mem_biUnion.mp (cCov zm)
  have own (a : V) (aT : a∈Q.T) (z : V) (za : z∈P a) :
      ∀ b∈Q.T,z∈P b → a=b := by
    intro b bt zb
    by_contra ne
    exact disjoint_left.mp (sep a aT b bt ne) za zb
  have charge (a : V) (aT : a∈Q.T) :
      1+D.card+(Q.missingSpare a).card+(Q.nearPartners a).card+(H a).card≤6 :=
    Q.rep_four_part_charge hc cap conn high dx n aT (full a aT) none
  have degX : G.degree x=A.card := by
    have eq : A=G.neighborFinset x := by
      ext z
      change z∈Shell G x 1 ↔ _
      rw [mem_shell,G.mem_neighborFinset,dist_eq_one_iff_adj]
    rw [eq,G.card_neighborFinset_eq_degree]
  have f1 (a : V) (aT : a∈Q.T) : (H a).card≤1 := by
    have h := charge a aT
    rcases shapes with s|s
    · change A.card=6 ∧ D.card=2 at s
      by_cases yes : ∃ z∈R,G.Adj (Q.rep a) z
      · obtain ⟨z,zm,e⟩ := yes
        obtain ⟨z1,zT⟩ := mem_sdiff.mp zm
        have k := Q.near_partners_full_of_spare_rep_neighbor hc aT
          (fun b bt _=>full b bt) z1 zT e
        omega
      have m : Q.missingSpare a=R := by
        apply eq_of_subset_of_card_le (filter_subset _ _)
        have sub : R⊆Q.missingSpare a := fun z zm=>mem_filter.mpr ⟨zm,fun e=>yes ⟨z,zm,e⟩⟩
        exact card_le_card sub
      rw [m] at h
      omega
    · change A.card=5 ∧ D.card=3 at s
      have ax : a≠x := by
        intro e
        have j := mem_shell.mp (Q.near aT)
        rw [e,dist_self] at j
        omega
      have ah := (high a x ax).resolve_right (by omega)
      have l := Q.selected_degree_le_two_add_spares_add_partners hc aT
      change G.degree a≤2+R.card+(Q.nearPartners a).card at l
      omega
  have f3zero (d3 : D.card=3) (a : V) (aT : a∈Q.T) : (H a).card=0 := by
    have as5 : A.card=5 := by
      change (A.card=6 ∧ D.card=2) ∨ (A.card=5 ∧ D.card=3) at shapes
      rcases shapes with k|k <;> omega
    have h := charge a aT
    have ax : a≠x := by
      intro e
      have j := mem_shell.mp (Q.near aT)
      rw [e,dist_self] at j
      omega
    have ah := (high a x ax).resolve_right (by omega)
    have l := Q.selected_degree_le_two_add_spares_add_partners hc aT
    change G.degree a≤2+R.card+(Q.nearPartners a).card at l
    omega
  obtain ⟨a,aT⟩ := card_pos.mp (show 0<Q.T.card by rw [Q.t3]; decide)
  let W := (Q.T.erase a).biUnion H
  have wc : W.card≤2 := by
    have u := card_biUnion_le_card_mul (Q.T.erase a) H 1
      (fun b bm=>f1 b (mem_erase.mp bm).2)
    rw [card_erase_of_mem aT,Q.t3] at u
    exact u
  let J := P a\W
  have jc : 2≤J.card := by
    have g := card_sdiff_add_card_eq_card (show P a ∩ W⊆P a from inter_subset_left)
    have w := card_le_card (show P a ∩ W⊆W from inter_subset_right)
    have eq : P a\(P a∩W)=J := by
      ext z
      simp [J]
    rw [eq,full a aT] at g
    omega
  obtain ⟨u,um,v,vm,uv⟩ := one_lt_card.mp (show 1<J.card by omega)
  obtain ⟨c,cj,ch⟩ : ∃ c∈J,6≤G.degree c :=
    (high u v uv).elim (fun q=>⟨u,um,q⟩) (fun q=>⟨v,vm,q⟩)
  obtain ⟨ca,cn⟩ := mem_sdiff.mp cj
  have no : ∀ z∈C,z∉P a → ¬G.Adj c z := by
    intro z zC za cz
    obtain ⟨b,bT,zb⟩ := group z zC
    have ba : b≠a := fun e=>za (e ▸ zb)
    have notB : c∉P b := fun h=>ba ((own a aT c ca b bT h).symm)
    have cm : c∈H b := mem_filter.mpr ⟨radius_four_group_sub_third none ca,notB,z,zb,cz.symm⟩
    exact cn (mem_biUnion.mpr ⟨b,mem_erase.mpr ⟨ba,bT⟩,cm⟩)
  have cPorts := Q.third_ports_of_no_cross hc aT ca ch none (own a aT c ca) no
  rw [full a aT] at cPorts
  change 6≤4+(L c).card at cPorts
  let Y := C\P a
  let F := Y.filter (fun z=>6≤G.degree z)
  have y8 : Y.card=8 := by
    have h := card_sdiff_add_card_eq_card (show P a⊆C from radius_four_group_sub_third none)
    rw [full a aT,c12] at h
    change Y.card+4=12 at h
    omega
  have low : (Y\F).card≤1 := by
    by_contra! over
    obtain ⟨i,im,j,jm,ij⟩ := one_lt_card.mp over
    obtain ⟨iY,iF⟩ := mem_sdiff.mp im
    obtain ⟨jY,jF⟩ := mem_sdiff.mp jm
    exact (high i j ij).elim (fun e=>iF (mem_filter.mpr ⟨iY,e⟩))
      (fun e=>jF (mem_filter.mpr ⟨jY,e⟩))
  have fSeven : 7≤F.card := by
    have h := card_sdiff_add_card_eq_card (show F⊆Y from filter_subset _ _)
    omega
  have crossNo (z : V) (zf : z∈F) : ¬G.Adj c z := by
    obtain ⟨zY,_⟩ := mem_filter.mp zf
    obtain ⟨zC,za⟩ := mem_sdiff.mp zY
    exact no z zC za
  have off : c∉F := fun h=>(mem_sdiff.mp (mem_filter.mp h).1).2 ca
  refine cross_port_overload hc cap (x:=x) F off fSeven crossNo ?_
  intro z zF
  obtain ⟨zY,zHigh⟩ := mem_filter.mp zF
  obtain ⟨zC,_⟩ := mem_sdiff.mp zY
  obtain ⟨b,bT,zb⟩ := group z zC
  have m := Q.third_degree_bound_of_unique_group hc bT zb none (own b bT z zb)
  rw [full b bT] at m
  change G.degree z≤4+(H b).card+(L z).card at m
  change (L c).card+(L z).card>D.card
  change (A.card=6 ∧ D.card=2) ∨ (A.card=5 ∧ D.card=3) at shapes
  rcases shapes with s|s
  · have kit := f1 b bT
    omega
  · have kit := f3zero s.2 b bT
    omega

end RadiusFiveNearEquality

#print axioms RadiusFiveNearEquality.no_order24_full_near_family
end Graffiti189LongestPath
