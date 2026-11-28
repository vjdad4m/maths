import DegreeFiveEightNoBridge189

namespace Graffiti189LongestPath.CrossSaturation.Split.Five
open SimpleGraph SimpleGraph.Walk Finset
open private d2 from CrossSaturation189
open private left_boundary from AdjacentCut189
open private not_common from DegreeFiveFourPort189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V} (S : Graffiti189LongestPath.CrossSaturation.Split G a b)
set_option linter.unusedSectionVars false

theorem no_bridge_route_at_four_four (hc : G.Connected) (far : 3≤G.dist a b)
    (even : ∀ x,(EvenFrom G x).card≤6)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (localFour : S.localA.card=4) (foreignFour : S.foreignA.card=4)
    (bFour : (S.L.filter (G.Adj b)).card≤4)
    (iFour : (S.L.filter (fun u=>¬G.Adj a u ∧ ¬G.Adj b u)).card≤4)
    (noBridge : ¬portBridge S)
    (near : ∀ u∈S.L,¬G.Adj a u → ¬G.Adj b u → ∃ x∈S.localA,G.Adj x u) :
    ∃ p,∃ q,G.Adj a p ∧ G.Adj b q ∧ RouteOn G S.L p q := by
  classical
  let A := S.localA
  let B := S.L.filter (G.Adj b)
  let I := S.L.filter (fun u=>¬G.Adj a u ∧ ¬G.Adj b u)
  have ⟨cl,full⟩ := no_bridge_port_nonports_complete S hc far even foreignFour noBridge near
  obtain ⟨x,xL,ax⟩ := S.leftA
  have xA : x∈A := mem_filter.mpr ⟨xL,ax⟩
  obtain ⟨u,uL,z,zL,au,bu,bz,_,uz,z2⟩ :=
    b_gateway_from_a_port_without_bridge S hc far even foreignFour noBridge xL ax
  have uI : u∈I := mem_filter.mpr ⟨uL,au,bu⟩
  have zB : z∈B := mem_filter.mpr ⟨zL,bz⟩
  have only (c : V) (cb : c∈B) (v : V) (vi : v∈I) (vc : G.Adj v c) : c=z := by
    obtain ⟨cL,bc⟩ := mem_filter.mp cb
    obtain ⟨vL,av,bv⟩ := mem_filter.mp vi
    have e : x≠c := fun eq=>not_common far ax (eq.symm ▸ bc)
    have no : ¬G.Adj x c := fun h=>noBridge ⟨x,xL,c,cL,ax,h,bc⟩
    have c2 := d2 hc e no (full x xA v vL av bv) vc
    exact singleton_local_distance_two_at_opposite_four S hc even foreignFour xL ax cL zL c2 z2
  have candidate (c v : V) (cb : c∈B) (cz : c≠z) (cv : G.Adj c v) :
      v=b ∨ v∈B := by
    obtain ⟨cL,bc⟩ := mem_filter.mp cb
    rcases left_boundary S c cL v cv with va|vb|vL
    · exact (not_common far (va ▸ cv.symm) bc).elim
    · exact .inl vb
    by_cases bv : G.Adj b v
    · exact .inr (mem_filter.mpr ⟨vL,bv⟩)
    have av : ¬G.Adj a v := fun h=>noBridge ⟨v,vL,c,cL,h,cv.symm,bc⟩
    exact (cz (only c cb v (mem_filter.mpr ⟨vL,av,bv⟩) cv.symm)).elim
  have low (c : V) (cb : c∈B) (cz : c≠z) : ¬5≤G.degree c := by
    have sub : G.neighborFinset c⊆insert b (B.erase c) := by
      intro v vm
      have cv := (mem_neighborFinset G c v).mp vm
      exact (candidate c v cb cz cv).elim
        (fun e=>mem_insert.mpr (.inl e))
        (fun m=>mem_insert_of_mem (mem_erase.mpr ⟨cv.ne.symm,m⟩))
    have m := (card_le_card sub).trans (card_insert_le b (B.erase c))
    rw [card_neighborFinset_eq_degree,card_erase_of_mem cb] at m
    change B.card≤4 at bFour
    have pos := card_pos.mpr ⟨c,cb⟩
    omega
  have few : (B.erase z).card≤1 := by
    apply Classical.byContradiction
    intro h
    obtain ⟨c,bc,d,bd,ne⟩ := one_lt_card.mp (by omega : 1<(B.erase z).card)
    exact (degree c d ne).elim
      (low c (mem_erase.mp bc).2 (mem_erase.mp bc).1)
      (low d (mem_erase.mp bd).2 (mem_erase.mp bd).1)
  have dis : Disjoint A I := disjoint_left.mpr (fun v va vi=>(mem_filter.mp vi).2.1 (mem_filter.mp va).2)
  have cap : I.card≤A.card := by
    change I.card≤4 at iFour
    change A.card=4 at localFour
    omega
  obtain ⟨p,pa,path⟩ := route_clique_join_end_leaf dis cl
    (fun h ha v vv=>by
      obtain ⟨vl,av,bv⟩ := mem_filter.mp (mem_erase.mp vv).2
      exact full h ha v vl av bv)
    cap xA uI (full x xA u uL au bu)
  have nz : z∉A∪I := by
    intro m
    exact (mem_union.mp m).elim
      (fun za=>not_common far (mem_filter.mp za).2 bz) (fun zi=>(mem_filter.mp zi).2.2 bz)
  have route := path.suffix uz nz
  have union : A∪I∪B=S.L := by
    ext v
    simp only [A,I,B,Split.localA,mem_union,mem_filter]
    by_cases av : G.Adj a v <;> by_cases bv : G.Adj b v <;> simp [av,bv]
  by_cases extra : (B.erase z).Nonempty
  · obtain ⟨c,ce⟩ := extra
    obtain ⟨cz,cb⟩ := mem_erase.mp ce
    have whole : B={z,c} := by
      have es : B.erase z={c} := eq_of_subset_of_card_le (by
        intro y ym
        by_contra no
        have ne : y≠c := fun e=>no (mem_singleton.mpr e)
        have pos := one_lt_card.mpr ⟨y,ym,c,ce,ne⟩
        omega) (by
          rw [card_singleton]
          exact card_pos.mpr ⟨c,ce⟩)
      rw [←insert_erase zB,es]
    obtain ⟨cL,bc⟩ := mem_filter.mp cb
    have cx : c≠x := fun e=>not_common far ax (e ▸ bc)
    let W := ↑(↑S.L : Set V)
    obtain ⟨w,wl,cw⟩ : ∃ w∈S.L,G.Adj c w := by
      obtain ⟨v⟩ := S.leftConnected.preconnected (⟨c,cL⟩ : W) ⟨x,xL⟩
      cases v with
      | nil => exact (cx rfl).elim
      | @cons c w x d q => exact ⟨w.val,w.property,d⟩
    have wb := (candidate c w cb cz cw).resolve_left (fun e=>S.leftOff.2 (e ▸ wl))
    have wz : w=z := by
      have cases' : w=z ∨ w=c := by simpa [whole] using wb
      exact cases'.resolve_right cw.ne.symm
    have nc : c∉insert z (A∪I) := by
      intro h
      rcases mem_insert.mp h with ce|h
      · exact cz ce
      exact (mem_union.mp h).elim (fun ca=>not_common far (mem_filter.mp ca).2 bc)
        (fun ci=>(mem_filter.mp ci).2.2 bc)
    have q := route.suffix ((wz ▸ cw).symm) nc
    have eq : insert c (insert z (A∪I))=S.L := by
      rw [←union,whole]
      ext v
      simp [or_comm,or_left_comm,or_assoc]
    exact ⟨p,c,(mem_filter.mp pa).2,bc,eq ▸ q⟩
  have whole : B={z} := by
    have e : B.erase z=∅ := Finset.eq_empty_iff_forall_not_mem.mpr (fun y ym=>extra ⟨y,ym⟩)
    calc
      B = insert z (B.erase z) := (insert_erase zB).symm
      _ = {z} := by simp [e]
  have eq : insert z (A∪I)=S.L := by
    rw [←union,whole]
    ext v
    simp [or_comm,or_left_comm,or_assoc]
  exact ⟨p,z,(mem_filter.mp pa).2,bz,eq ▸ route⟩

#print axioms no_bridge_route_at_four_four
end Graffiti189LongestPath.CrossSaturation.Split.Five
