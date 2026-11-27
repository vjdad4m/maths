import DegreeFiveTwoTwoCommonGeometry189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private Shore shore_off shore_closed shore_connected from DegreeFiveActualCut189
open private secondShore from DegreeFiveDistanceTwoThreeClose189
open private Cmp portColor from DegreeFiveThreeForeignImpossible189
open private sharedPortSet inside_high_at_least_four_if_exclusive from DegreeFiveBalancedCommonRoot189
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

/-- A genuinely asymmetric common shore (four contacts to a, three
to b) has order four and a low a-only vertex. -/
theorem low_a_porter_of_four_three_opposite_two_two
    (hc : G.Connected)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5 ≤ G.degree u ∨ 5 ≤ G.degree v)
    {C : Cmp (G:=G) (a:=a) (b:=b)}
    (shared : 3 ≤ (sharedPortSet C).card)
    (size : (Shore C).card ≤ (sharedPortSet C).card+3)
    (oneB : (secondShore C b).card ≤ 1)
    (cA : (portColor C a).card=4) (cB : (portColor C b).card=3) :
    (Shore C).card=4 ∧ (secondShore C b).card=1 ∧
    ∃ z∈Shore C,G.Adj a z ∧ G.dist z b=2 ∧ G.degree z<5 := by
  classical
  let S := Shore C
  let A := portColor C a
  let B := portColor C b
  let K := sharedPortSet C
  let N := S\B
  let H := N.filter (fun z=>5 ≤ G.degree z)
  have bSub : B⊆S := filter_subset _ _
  have aSub : A⊆S := filter_subset _ _
  have kSub : K⊆B := fun _ h=>mem_filter.mpr ⟨(mem_filter.mp h).1,(mem_filter.mp h).2.2⟩
  have b3 : B.card=3 := cB
  have a4 : A.card=4 := cA
  have k3 : K.card=3 := by
    have k := card_le_card kSub
    have p : 3 ≤ K.card := shared
    omega
  have kEq : K=B := eq_of_subset_of_card_le kSub (by omega)
  have ba : B⊆A := by
    intro w wb
    have k : w∈K := kEq.symm ▸ wb
    exact mem_filter.mpr ⟨(mem_filter.mp k).1,(mem_filter.mp k).2.1⟩
  have sLo : 4 ≤ S.card := by
    have q := card_le_card aSub
    omega
  have sHi : S.card ≤ 6 := by
    have q : S.card ≤ K.card+3 := size
    omega
  have sn : N.card+B.card=S.card := card_sdiff_add_card_eq_card bSub
  have part : (N\H).card+H.card=N.card := card_sdiff_add_card_eq_card (filter_subset _ _)
  have miss_b {w : V} (wn : w∈N) : ¬G.Adj b w :=
    fun h=>(mem_sdiff.mp wn).2 (mem_filter.mpr ⟨(mem_sdiff.mp wn).1,h⟩)
  have into_b {w y : V} (wn : w∈N) (yb : y∈B) (wy : G.Adj w y) :
      w∈secondShore C b := by
    have ws := (mem_sdiff.mp wn).1
    have ne : b≠w := fun e=>(shore_off C).2 (Eq.mp (congrArg (fun v : V => v∈Shore C) e.symm)
      (show w∈Shore C from ws))
    exact mem_inter.mpr ⟨ws,d2 hc ne (miss_b wn) (mem_filter.mp yb).2 wy.symm⟩
  have inner (w : V) : inside G S w⊆S.erase w := by
    intro y ym
    obtain ⟨ys,wy⟩ := mem_filter.mp ym
    exact mem_erase.mpr ⟨wy.ne.symm,ys⟩
  have high_inner {w : V} (wn : w∈N) (wh : 5 ≤ G.degree w) : 4 ≤ (inside G S w).card :=
    inside_high_at_least_four_if_exclusive (mem_sdiff.mp wn).1 wh (fun p=>miss_b wn p.2)
  have hSub : H⊆secondShore C b := by
    intro w wh
    obtain ⟨wn,hi⟩ := mem_filter.mp wh
    have hit : ∃ y∈B,G.Adj w y := by
      apply Classical.byContradiction
      intro no
      have sub : inside G S w⊆N := by
        intro t tm
        obtain ⟨ts,wt⟩ := mem_filter.mp tm
        exact mem_sdiff.mpr ⟨ts,fun tb=>no ⟨t,tb,wt⟩⟩
      have h := card_le_card sub
      have q := high_inner wn hi
      omega
    obtain ⟨y,yb,wy⟩ := hit
    exact into_b wn yb wy
  have h1 := (card_le_card hSub).trans oneB
  have low1 : (N\H).card ≤ 1 := by
    apply Classical.byContradiction
    intro n
    obtain ⟨x,xm,y,ym,xy⟩ := one_lt_card.mp (show 1<(N\H).card by omega)
    have low (z : V) (zm : z∈N\H) : ¬5 ≤ G.degree z :=
      fun h=>(mem_sdiff.mp zm).2 (mem_filter.mpr ⟨(mem_sdiff.mp zm).1,h⟩)
    exact (degree x y xy).elim (low x xm) (low y ym)
  have s5 : S.card ≤ 5 := by omega
  have s4 : S.card=4 := by
    apply Classical.byContradiction
    intro no
    have large : S.card=5 := by omega
    have n2 : N.card=2 := by omega
    obtain ⟨w,wh⟩ := card_pos.mp (show 0<H.card by omega)
    obtain ⟨z,zl⟩ := card_pos.mp (show 0<(N\H).card by omega)
    obtain ⟨wn,w5⟩ := mem_filter.mp wh
    obtain ⟨zn,zh⟩ := mem_sdiff.mp zl
    have ws := (mem_sdiff.mp wn).1
    have zs := (mem_sdiff.mp zn).1
    have wz : w≠z := fun eq=>zh (eq ▸ wh)
    have nEq : N={w,z} := (eq_of_subset_of_card_le (by
      intro t tm
      rcases mem_insert.mp tm with rfl|t
      · exact wn
      obtain rfl := mem_singleton.mp t
      exact zn) (by simp [wz,n2])).symm
    have aw : G.Adj a w := by
      apply Classical.byContradiction
      intro nn
      have sub : G.neighborFinset w⊆S.erase w := by
        intro y ym
        have wy := (mem_neighborFinset G _ _).mp ym
        rcases shore_closed C w ws y wy with rfl|rfl|ys
        · exact (nn wy.symm).elim
        · exact (miss_b wn wy.symm).elim
        exact mem_erase.mpr ⟨wy.ne.symm,ys⟩
      have h := card_le_card sub
      rw [card_neighborFinset_eq_degree,card_erase_of_mem ws] at h
      omega
    have az : ¬G.Adj a z := by
      intro zz
      have sub : insert w (insert z B)⊆A := by
        intro t tm
        rcases mem_insert.mp tm with rfl|tm
        · exact mem_filter.mpr ⟨ws,aw⟩
        rcases mem_insert.mp tm with rfl|tm
        · exact mem_filter.mpr ⟨zs,zz⟩
        exact ba tm
      have nw : w∉B := (mem_sdiff.mp wn).2
      have nz : z∉B := (mem_sdiff.mp zn).2
      have h := card_le_card sub
      rw [card_insert_of_not_mem (by simpa [wz] using nw),card_insert_of_not_mem nz] at h
      omega
    let P : Set V := (↑({w} : Finset V) : Set V)ᶜ
    let zP : P := ⟨z,by simp [P,wz.symm]⟩
    have wb : w≠b := fun e=>(shore_off C).2 (Eq.mp (congrArg (fun v : V => v∈Shore C) e) (show w∈Shore C from ws))
    let bP : P := ⟨b,by simp [P,wb.symm]⟩
    have reachFirst {x y : P} (p : (G.induce P).Walk x y) :
        x=y ∨ ∃ t : P,(G.induce P).Adj x t := by
      cases p with
      | nil => exact .inl rfl
      | @cons _ k _ h p => exact .inr ⟨k,h⟩
    obtain ⟨p⟩ := (conn {w} (by simp)).preconnected zP bP
    have ne : zP≠bP := fun e=>(shore_off C).2
      (Eq.mp (congrArg (fun v : V => v∈Shore C) (congrArg Subtype.val e)) zs)
    obtain ⟨t,h⟩ := (reachFirst p).resolve_left ne
    have zt : G.Adj z t.val := h
    have tb : t.val∈B := by
      have ts : t.val∈S := by
        rcases shore_closed C z zs t.val zt with e|e|ts
        · exact (az (e ▸ zt.symm)).elim
        · exact (miss_b zn (e ▸ zt.symm)).elim
        exact ts
      apply Classical.byContradiction
      intro nn
      have tn : t.val∈N := mem_sdiff.mpr ⟨ts,nn⟩
      rw [nEq] at tn
      have tw : t.val≠w := by simpa [P] using t.property
      rcases mem_insert.mp tn with eq|tm
      · exact tw eq
      exact zt.ne (mem_singleton.mp tm).symm
    have h := one_lt_card.mpr ⟨w,hSub wh,z,into_b zn tb zt,wz⟩
    omega
  obtain ⟨z,zn⟩ := card_pos.mp (show 0<N.card by omega)
  have zs := (mem_sdiff.mp zn).1
  have eqA : A=S := eq_of_subset_of_card_le aSub (by omega)
  have za : G.Adj a z := (mem_filter.mp (show z∈A by rwa [eqA])).2
  have lo : G.degree z<5 := by
    apply Classical.byContradiction
    intro bad
    have h := high_inner zn (by omega)
    have k := card_le_card (inner z)
    rw [card_erase_of_mem zs] at k
    omega
  have qeq : N={z} := (eq_of_subset_of_card_le (by simpa using zn) (by simp; omega)).symm
  obtain ⟨x,xb⟩ := card_pos.mp (show 0<B.card by omega)
  have xs := bSub xb
  let U := ↑(↑S : Set V)
  obtain ⟨p⟩ := (shore_connected C).preconnected (⟨z,zs⟩ : U) ⟨x,xs⟩
  have first {v w : U} (q : (G.induce (↑S : Set V)).Walk v w) :
      v=w ∨ ∃ j : U,(G.induce (↑S : Set V)).Adj v j := by
    cases q with
    | nil => exact .inl rfl
    | @cons _ k _ e q => exact .inr ⟨k,e⟩
  obtain ⟨r,edge⟩ := (first p).resolve_left (fun e=>(mem_sdiff.mp zn).2
    (Eq.mp (congrArg (fun v : V => v∈B) (show x=z from (congrArg Subtype.val e).symm)) xb))
  have zr : G.Adj z r.val := edge
  have rb : r.val∈B := by
    apply Classical.byContradiction
    intro no
    have m : r.val∈N := mem_sdiff.mpr ⟨r.property,no⟩
    rw [qeq] at m
    exact zr.ne (mem_singleton.mp m).symm
  have zz := into_b zn rb zr
  have nonempty := card_pos.mpr ⟨z,zz⟩
  have bdist : G.dist b z=2 := (mem_filter.mp (mem_inter.mp zz).2).2
  exact ⟨s4,by omega,z,zs,za,by rwa [SimpleGraph.dist_comm],lo⟩

#print axioms low_a_porter_of_four_three_opposite_two_two
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
