import DegreeFiveOneFourShapes189
import DegreeFiveThreeFiveDom189


namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset
open private Shore shore_off shore_closed shore_disjoint shore_nonempty shore_connected shore_hit_a shore_hit_b from DegreeFiveActualCut189
open private singleton_shore_of_one_port from DegreeFiveOneFourShapes189
open private two_walk_middle from DistanceTwoCut189
open private secondShore from DegreeFiveDistanceTwoThreeClose189
open private Cmp two_shore_budget count_cut_degree_on_two_shores portColor from DegreeFiveThreeForeignImpossible189
open private four_in_nonsingleton from DegreeFiveDistanceTwoThreeClose189
open private nonport_neighbors_subset from DegreeFiveThreeFiveShapes189
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

theorem one_five_shore_shape
    (two : G.dist a b=2)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    (one : (cutPorts C).card=1) (five : (cutPorts D).card=5) :
    ∃ r,Shore C={r} ∧ G.Adj a r ∧ G.Adj b r ∧
      (∀ v∈Shore D,5≤G.degree v) ∧
      ∀ c : V,c=a ∨ c=b → 4≤(portColor D c).card := by
  classical
  obtain ⟨r,rp⟩ := card_pos.mp (show 0<(cutPorts C).card by omega)
  have ce := singleton_shore_of_one_port conn cd one rp
  have rc : r∈Shore C := by simp [ce]
  have ab : a≠b := by intro h; rw [h,dist_self] at two; omega
  obtain ⟨u,uc,au⟩ := shore_hit_a ab conn C
  obtain ⟨v,vc,bv⟩ := shore_hit_b ab conn C
  have ar : G.Adj a r := (show u=r by simpa [ce] using uc) ▸ au
  have br : G.Adj b r := (show v=r by simpa [ce] using vc) ▸ bv
  have rlow : ¬5≤G.degree r := by
    have sub : G.neighborFinset r⊆({a,b} : Finset V) := by
      intro z zp
      have rz := (mem_neighborFinset G r z).mp zp
      rcases shore_closed C r rc z rz with h|h|h
      · simp [h]
      · simp [h]
      exact (rz.ne.symm (by simpa [ce] using h)).elim
    have m := card_le_card sub
    rw [card_neighborFinset_eq_degree] at m
    simp [ab] at m
    omega
  have a5 := (degree a r (fun e=>(shore_off C).1 (e.symm ▸ rc))).resolve_right rlow
  have b5 := (degree b r (fun e=>(shore_off C).2 (e.symm ▸ rc))).resolve_right rlow
  have high (z : V) (zd : z∈Shore D) : 5≤G.degree z :=
    (degree r z (fun e=>disjoint_left.mp (shore_disjoint cd) rc (e.symm ▸ zd))).resolve_left rlow
  refine ⟨r,ce,ar,br,high,?_⟩
  intro c cut
  have hi : 5≤G.degree c := cut.elim (fun e=>e.symm ▸ a5) (fun e=>e.symm ▸ b5)
  have count := count_cut_degree_on_two_shores cd cover two cut
  have le : (portColor C c).card≤1 :=
    (card_le_card (filter_subset _ _)).trans (by simp [ce])
  omega

theorem one_five_opposite_order_bound
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    (one : (cutPorts C).card=1) (five : (cutPorts D).card=5) :
    (Shore D).card≤13 ∧
      ((∃ c : V,(c=a ∨ c=b) ∧ ∀ z∈cutPorts D,G.Adj c z) → (Shore D).card≤9) := by
  classical
  obtain ⟨r,ce,ar,br,high,colors⟩ := one_five_shore_shape two conn degree cd cover one five
  have rc : r∈Shore C := by simp [ce]
  have dom := (saturated_common_foreign_port_domination hc even cd five rc ar br).2
  let F := Shore D \ cutPorts D
  let A := secondShore D a
  let B := secondShore D b
  have ac : A.card≤4 := by
    have h := two_shore_budget cd ⟨(shore_off C).2,(shore_off D).2⟩ two even
    change (secondShore C a).card+A.card≤4 at h
    omega
  have bc : B.card≤4 := by
    have h := two_shore_budget cd ⟨(shore_off C).1,(shore_off D).1⟩ (by rwa [dist_comm]) even
    change (secondShore C b).card+B.card≤4 at h
    omega
  have charge {c z w : V} (cut : c=a ∨ c=b) (zf : z∈F)
      (cw : G.Adj c w) (zw : G.Adj z w) : z∈secondShore D c := by
    obtain ⟨zd,zp⟩ := mem_sdiff.mp zf
    have no : ¬G.Adj c z := fun e=>zp (mem_filter.mpr
      ⟨zd,cut.elim (fun h=>.inl (h ▸ e)) (fun h=>.inr (h ▸ e))⟩)
    have ne : c≠z := fun e=>cut.elim
      (fun ca=>(shore_off D).1 ((ca.symm.trans e).symm ▸ zd))
      (fun cb=>(shore_off D).2 ((cb.symm.trans e).symm ▸ zd))
    exact mem_inter.mpr ⟨zd,d2 hc ne no cw zw.symm⟩
  have fSub : F⊆A∪B := by
    intro z zf
    obtain ⟨zd,zp⟩ := mem_sdiff.mp zf
    obtain ⟨w,wp,zw⟩ := dom z zd zp
    rcases (mem_filter.mp wp).2 with aw|bw
    · exact mem_union_left _ (charge (.inl rfl) zf aw zw)
    exact mem_union_right _ (charge (.inr rfl) zf bw zw)
  have tally : F.card+5=(Shore D).card := by
    have h : F.card+(cutPorts D).card=(Shore D).card :=
      card_sdiff_add_card_eq_card (filter_subset _ _)
    rwa [five] at h
  have fCap := (card_le_card fSub).trans (card_union_le A B)
  refine ⟨by omega,?_⟩
  rintro ⟨c,cc,all⟩
  have sub : F⊆secondShore D c := by
    intro z zf
    obtain ⟨zd,zp⟩ := mem_sdiff.mp zf
    obtain ⟨w,wp,zw⟩ := dom z zd zp
    exact charge cc zf (all w wp) zw
  have upper := card_le_card sub
  rcases cc with e|e
  · rw [e] at upper
    change F.card≤A.card at upper
    omega
  rw [e] at upper
  change F.card≤B.card at upper
  omega

theorem one_five_two_distinct_ports_have_opposite_choices
    {D : Cmp (G:=G) (a:=a) (b:=b)}
    (five : (cutPorts D).card=5)
    (color : ∀ c : V,c=a ∨ c=b → 4≤(portColor D c).card)
    {x y : V} (xp : x∈cutPorts D) (yp : y∈cutPorts D) (xy : x≠y) :
    (G.Adj a x ∧ G.Adj b y) ∨ (G.Adj b x ∧ G.Adj a y) := by
  classical
  have noPair (c : V) (h : c=a ∨ c=b) : ¬(¬G.Adj c x ∧ ¬G.Adj c y) := by
    rintro ⟨cx,cy⟩
    have sub : portColor D c⊆cutPorts D := by
      intro z zc
      obtain ⟨zd,cz⟩ := mem_filter.mp zc
      exact mem_filter.mpr ⟨zd,h.elim (fun e=>.inl (e ▸ cz)) (fun e=>.inr (e ▸ cz))⟩
    have sub' : portColor D c⊆((cutPorts D).erase x).erase y := by
      intro z zc
      obtain ⟨_,cz⟩ := mem_filter.mp zc
      exact mem_erase.mpr ⟨fun e=>cy (e ▸ cz),mem_erase.mpr ⟨fun e=>cx (e ▸ cz),sub zc⟩⟩
    have cap := card_le_card sub'
    rw [card_erase_of_mem (mem_erase.mpr ⟨xy.symm,yp⟩),card_erase_of_mem xp,five] at cap
    have dlo := color c h
    omega
  have ha := noPair a (.inl rfl)
  have hb := noPair b (.inr rfl)
  have x := (mem_filter.mp xp).2
  have y := (mem_filter.mp yp).2
  tauto

#print axioms one_five_shore_shape
#print axioms one_five_opposite_order_bound
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
