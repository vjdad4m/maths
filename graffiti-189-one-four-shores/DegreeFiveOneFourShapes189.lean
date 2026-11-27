import DegreeFiveTwoFourShapes189


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

private theorem singleton_shore_of_one_port
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (one : (cutPorts C).card=1) {r : V} (rp : r∈cutPorts C) :
    Shore C={r} := by
  classical
  have pe : cutPorts C={r} := (eq_of_subset_of_card_le (singleton_subset_iff.mpr rp) (by simp [one])).symm
  have rC := (mem_filter.mp rp).1
  have sub : Shore C⊆{r} := by
    intro z zC
    apply mem_singleton.mpr
    apply Classical.byContradiction
    intro zr
    obtain ⟨w,wD⟩ := shore_nonempty D
    have wr : w≠r := fun e=>disjoint_left.mp (shore_disjoint cd) rC (e ▸ wD)
    let U := ((↑({r} : Finset V) : Set V)ᶜ)
    have zz : z∈U := by simp [U,zr]
    have ww : w∈U := by simp [U,wr]
    have closed {v t : U} (e : (G.induce U).Adj v t) (vc : v.val∈Shore C) :
        t.val∈Shore C := by
      have vr : v.val≠r := by simpa [U] using v.property
      have no : v.val∉cutPorts C := by simp [pe,vr]
      have adj : G.Adj v.val t.val := e
      rcases shore_closed C v.val vc t.val adj with h|h|h
      · exact (no (mem_filter.mpr ⟨vc,.inl (h ▸ adj.symm)⟩)).elim
      · exact (no (mem_filter.mpr ⟨vc,.inr (h ▸ adj.symm)⟩)).elim
      exact h
    have along {v t : U} (p : (G.induce U).Walk v t) :
        v.val∈Shore C → t.val∈Shore C := by
      induction p with
      | nil => exact id
      | cons e p ih => exact fun h=>ih (closed e h)
    obtain ⟨p⟩ := (conn {r} (by simp)).preconnected (⟨z,zz⟩ : U) ⟨w,ww⟩
    exact disjoint_left.mp (shore_disjoint cd) (along p zC) wD
  exact eq_of_subset_of_card_le sub (card_le_card (singleton_subset_iff.mpr rC))

theorem one_four_shore_shape
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    (one : (cutPorts C).card=1) (four : (cutPorts D).card=4) :
    ∃ r,Shore C={r} ∧ G.Adj a r ∧ G.Adj b r ∧
      (∀ v∈Shore D,5≤G.degree v) ∧ (Shore D).card≤8 := by
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
  have pure (c : V) (cut : c=a ∨ c=b) (h : 5≤G.degree c) :
      ∀ z∈cutPorts D,G.Adj c z := by
    have count := count_cut_degree_on_two_shores cd cover two cut
    have le : (portColor C c).card≤1 := (card_le_card (filter_subset _ _)).trans (by simp [ce])
    have sub : portColor D c⊆cutPorts D := by
      intro z zc
      obtain ⟨zd,cz⟩ := mem_filter.mp zc
      exact mem_filter.mpr ⟨zd,cut.elim (fun e=>.inl (e ▸ cz)) (fun e=>.inr (e ▸ cz))⟩
    have eq : portColor D c=cutPorts D := eq_of_subset_of_card_le sub (by omega)
    intro z zp
    exact (mem_filter.mp (eq.symm ▸ zp)).2
  have allA := pure a (.inl rfl) a5
  obtain ⟨_,_,budget,dom⟩ := four_foreign_near_with_exception hc two even conn cd cover four rc ar br
  let F := Shore D \ cutPorts D
  let L := F.filter (fun z=>G.dist r z≠4)
  let Q := univ.filter (fun z=>G.dist r z=4)
  have exposed : L⊆secondShore D a := by
    intro z zl
    obtain ⟨zf,no4⟩ := mem_filter.mp zl
    obtain ⟨zd,zp⟩ := mem_sdiff.mp zf
    obtain ⟨w,wp,zw⟩ := (dom z zd zp).resolve_left no4
    have ne : a≠z := fun e=>(shore_off D).1 (e.symm ▸ zd)
    have no : ¬G.Adj a z := fun e=>zp (mem_filter.mpr ⟨zd,.inl e⟩)
    exact mem_inter.mpr ⟨zd,d2 hc ne no (allA w wp) zw.symm⟩
  have l4 : L.card≤4 := (card_le_card exposed).trans (by
    have sum := two_shore_budget cd ⟨(shore_off C).2,(shore_off D).2⟩ two even
    omega)
  have q1 : Q.card+(secondShore C r).card≤1 := budget
  have exc : F\L⊆Q := by
    intro z h
    obtain ⟨zf,zl⟩ := mem_sdiff.mp h
    have eq : G.dist r z=4 := Classical.byContradiction (fun n=>zl (mem_filter.mpr ⟨zf,n⟩))
    exact mem_filter.mpr ⟨mem_univ _,eq⟩
  have n := card_le_card exc
  have count : (F\L).card+L.card=F.card := card_sdiff_add_card_eq_card (filter_subset _ _)
  have total : F.card+4=(Shore D).card := by
    have h : F.card+(cutPorts D).card=(Shore D).card := card_sdiff_add_card_eq_card (filter_subset _ _)
    rwa [four] at h
  have Fvis : F⊆L := by
    intro z zF
    apply Classical.byContradiction
    intro zl
    have d4 : G.dist r z=4 := (mem_filter.mp (exc (mem_sdiff.mpr ⟨zF,zl⟩))).2
    obtain ⟨zd,zp⟩ := mem_sdiff.mp zF
    have low : G.neighborFinset z⊆F.erase z := by
      intro w wp
      obtain ⟨wz,wd⟩ := mem_erase.mp (nonport_neighbors_subset zd zp wp)
      refine mem_erase.mpr ⟨wz,mem_sdiff.mpr ⟨wd,?_⟩⟩
      intro port
      have rw : G.dist r w≤2 := by
        have walk := G.dist_le (SimpleGraph.Walk.cons ar.symm (allA w port).toWalk)
        simpa using walk
      have wz1 := dist_eq_one_iff_adj.mpr ((mem_neighborFinset G z w).mp wp).symm
      have tri := hc.dist_triangle (u:=r) (v:=w) (w:=z)
      omega
    have q := card_le_card low
    rw [card_neighborFinset_eq_degree,card_erase_of_mem zF] at q
    have h := high z zd
    omega
  have f4 := (card_le_card Fvis).trans l4
  exact ⟨r,ce,ar,br,high,by omega⟩

#print axioms one_four_shore_shape
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
