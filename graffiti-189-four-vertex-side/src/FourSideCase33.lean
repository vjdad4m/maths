import InnerFour189
namespace Graffiti189LongestPath.TwoCut.FourSideCtx
open SimpleGraph SimpleGraph.Walk Finset
open Graffiti189LongestPath.FourCut.Three
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {a b : V} {S : CutPair G a b} (C : FourSideCtx S)
set_option maxHeartbeats 2200000
set_option linter.unusedSectionVars false

private theorem single_inner_peers {x z : V} (xa : x∈C.A)
    (A3 : C.A.card=3) (high : 4≤G.degree x)
    (Eone : ∀ u∈C.E, G.Adj x u → u=z) :
    G.Adj x z ∧ ∀ y∈C.A, x≠y → G.Adj x y := by
  have sub : G.neighborFinset x⊆insert a (insert z (C.A.erase x)) := by
    intro y hy
    rcases mem_insert.mp (C.local_A_neighbor_sub xa hy) with rfl|q
    · exact mem_insert_self _ _
    rcases mem_union.mp q with m|m
    · exact mem_insert_of_mem (mem_insert_of_mem m)
    · exact mem_insert_of_mem (mem_insert.mpr (Or.inl (Eone y m ((mem_neighborFinset G x y).mp hy))))
  have eq := eq_of_subset_of_card_le sub (by
    have c := card_insert_le a (insert z (C.A.erase x))
    have d := card_insert_le z (C.A.erase x)
    rw [card_erase_of_mem xa,A3] at d
    rw [card_neighborFinset_eq_degree]
    omega)
  constructor
  · apply (mem_neighborFinset G x z).mp
    rw [eq]
    exact mem_insert_of_mem (mem_insert_self _ _)
  · intro y ya xy
    apply (mem_neighborFinset G x y).mp
    rw [eq]
    exact mem_insert_of_mem (mem_insert_of_mem (mem_erase.mpr ⟨xy.symm,ya⟩))

private theorem contra_33_unbalanced
    (A3 : C.A.card=3) (B3 : C.B.card=3) (U1 : C.U.card=1)
    (ipos : 1≤C.I.card) : False := by
  have ia := C.I_in_E_of_three A3
  have ib : C.I⊆C.F := by simpa only [C.swap_I] using C.swap.I_in_E_of_three B3
  have cp := C.e_cap
  have ibd := card_le_card ia
  have I1 : C.I.card=1 := by omega
  have eI := eq_of_subset_of_card_le ia (by omega)
  have no : ∀ x∈C.A,∀ y∈C.B,¬G.Adj x y := fun _ xa _ yb => C.no_cross_of_E_sub_I (by rw [←eI]) xa yb
  obtain ⟨r,rI⟩ := card_eq_one.mp I1
  have rF : r∈C.F := ib (by simp [rI])
  obtain ⟨y,yb,yr⟩ := C.swap.local_a_witness rF
  let Ahi := C.A.filter (fun x => 4≤G.degree x)
  have qsub : Ahi⊆DistanceTwo G y := by
    intro x hx
    obtain ⟨xa,xhi⟩ := mem_filter.mp hx
    obtain ⟨u,ue,xu⟩ := C.high_port_has_E xa xhi
    have uri : u∈C.I := eI.symm ▸ ue
    have eq : u=r := by simpa [rI] using uri
    exact C.swap.d2_cross_group yb xa (fun h => no x xa y yb h.symm)
      yr (eq ▸ xu.symm)
  have cap := C.swap.local_d2_cap yb ((filter_subset _ _).trans C.A_sub_H) qsub
  change Ahi.card+C.W.card≤4 at cap
  let Alo := C.A.filter (fun x => ¬4≤G.degree x)
  have alow : Alo.card≤1 := card_le_one.mpr (by
    intro x hx y hy
    exact Classical.byContradiction (fun ne =>
      (S.degree x y ne).elim (mem_filter.mp hx).2 (mem_filter.mp hy).2))
  have ca : Ahi.card + Alo.card=C.A.card := filter_card_add_filter_neg_card_eq_card _
  have pks := C.port_K_sum
  have wc := C.swap.Ucap
  change C.W.card≤3 at wc
  have W2 : C.W.card=2 := by omega
  have w := card_sdiff_add_card_eq_card
    (show C.U∪C.W⊆C.K from union_subset (fun _ h => (C.memU.mp h).1) (fun _ h => (C.memW.mp h).1))
  rw [card_union_of_disjoint C.dis_UW] at w
  have ck : C.K.card=4 := C.size
  obtain ⟨v,hv⟩ := card_pos.mp (show 0<(C.K\(C.U∪C.W)).card by omega)
  obtain ⟨vk,vp⟩ := mem_sdiff.mp hv
  have low : ¬4≤G.degree v := by
    intro hi
    have sub : G.neighborFinset v⊆C.K.erase v := by
      intro t ht
      have vt := (mem_neighborFinset G v t).mp ht
      rcases S.closed C.i v vk t vt with rfl|rfl|tk
      · exact (vp (mem_union.mpr (Or.inl (C.memU.mpr ⟨vk,vt.symm⟩)))).elim
      · exact (vp (mem_union.mpr (Or.inr (C.memW.mpr ⟨vk,vt.symm⟩)))).elim
      · exact mem_erase.mpr ⟨vt.ne.symm,tk⟩
    have le := card_le_card sub
    rw [card_neighborFinset_eq_degree,card_erase_of_mem vk,ck] at le
    omega
  have no_low : C.A⊆Ahi := by
    intro x xa
    have ne : x≠v := fun e => disjoint_left.mp C.dis_KH vk (e ▸ C.A_sub_H xa)
    exact mem_filter.mpr ⟨xa,(S.degree x v ne).resolve_right low⟩
  have cl := card_le_card no_low
  omega

private theorem contra_33_one_inner_ordered (A3 : C.A.card=3) (B3 : C.B.card=3)
    (U2 : C.U.card=2) (W2 : C.W.card=2) (I1 : C.I.card=1)
    (Bhi : ∀ x∈C.B,4≤G.degree x) : False := by
  have inE := C.I_in_E_of_three A3
  have inF : C.I⊆C.F := by simpa only [C.swap_I] using C.swap.I_in_E_of_three B3
  have ecap := C.e_cap
  have fcap := C.swap.e_cap
  change C.F.card≤C.W.card at fcap
  obtain ⟨r,Ieq⟩ := card_eq_one.mp I1
  have rI : r∈C.I := by simp [Ieq]
  have rE := inE rI
  have rF := inF rI
  have only_no_cross {x z : V} (xa : x∈C.A) (ze : z∈C.E) (xz : G.Adj x z)
      (no : ∀ v∈C.B,¬G.Adj x v) : z=r := by
    rcases C.classifyH (C.E_sub_H ze) with za|zb|zi
    · exact (disjoint_left.mp C.E_dis_A ze za).elim
    · exact (no z zb xz).elim
    · simpa [Ieq] using zi
  have only_no_cross_B {x z : V} (xb : x∈C.B) (ze : z∈C.F) (xz : G.Adj x z)
      (no : ∀ v∈C.A,¬G.Adj x v) : z=r := by
    rcases C.classifyH (C.swap.E_sub_H ze) with za|zb|zi
    · exact (no z za xz).elim
    · exact (disjoint_left.mp C.swap.E_dis_A ze zb).elim
    · simpa [Ieq] using zi
  by_cases cross : ∃ x∈C.A,∃ y∈C.B,G.Adj x y
  · obtain ⟨x0,xA,y0,yB,xy⟩ := cross
    have yE := C.local_a_d2 xA (C.B_sub_H yB) (fun h => disjoint_left.mp C.dis_AB h yB) xy
    have xF := C.swap.local_a_d2 yB (C.A_sub_H xA) (fun h => disjoint_left.mp C.dis_AB xA h) xy.symm
    have xr : x0≠r := fun h => C.I_not_A rI (h ▸ xA)
    have yr : y0≠r := fun h => C.I_not_B rI (h ▸ yB)
    have Eeq : C.E={y0,r} := (eq_of_subset_of_card_le
      (fun x hx => (mem_insert.mp hx).elim (fun e => e.symm ▸ yE) (fun h => (mem_singleton.mp h).symm ▸ rE))
      (by simp [yr]; omega)).symm
    have Feq : C.F={x0,r} := (eq_of_subset_of_card_le
      (fun x hx => (mem_insert.mp hx).elim (fun e => e.symm ▸ xF) (fun h => (mem_singleton.mp h).symm ▸ rF))
      (by simp [xr]; omega)).symm
    obtain ⟨u,hue,uh⟩ := C.high_of_two (show 2≤(C.A.erase x0).card by
      rw [card_erase_of_mem xA,A3])
    obtain ⟨un,ua⟩ := mem_erase.mp hue
    have u_no (y : V) (yb : y∈C.B) : ¬G.Adj u y := by
      intro e
      have f := C.swap.local_a_d2 yb (C.A_sub_H ua) (fun h => disjoint_left.mp C.dis_AB ua h) e.symm
      change u∈C.F at f
      rw [Feq] at f
      rcases mem_insert.mp f with f|f
      · exact un f
      · exact C.I_not_A rI ((mem_singleton.mp f) ▸ ua)
    obtain ⟨ur,peer⟩ := C.single_inner_peers ua A3 uh (fun t te ut => only_no_cross ua te ut u_no)
    have sub : C.B⊆DistanceTwo G u := by
      intro y yb
      by_cases e : y=y0
      · subst y
        exact C.d2_cross_group ua yb (u_no y0 yb) (peer x0 xA un) xy
      have byno (v : V) (va : v∈C.A) : ¬G.Adj y v := by
        intro ed
        have d := C.local_a_d2 va (C.B_sub_H yb) (fun h => disjoint_left.mp C.dis_AB h yb) ed.symm
        rw [Eeq] at d
        rcases mem_insert.mp d with d|d
        · exact e d
        · exact C.I_not_B rI ((mem_singleton.mp d) ▸ yb)
      obtain ⟨t,tf,yt⟩ := C.swap.high_port_has_E yb (Bhi y yb)
      have tr := only_no_cross_B yb tf yt byno
      exact C.d2_cross_group ua yb (u_no y yb) ur (tr ▸ yt.symm)
    have h := C.local_d2_cap ua C.B_sub_H sub
    omega
  · obtain ⟨u,ua,uh⟩ := C.high_of_two (show 2≤C.A.card by omega)
    obtain ⟨t,te,ut⟩ := C.high_port_has_E ua uh
    have u_no (y : V) (yb : y∈C.B) : ¬G.Adj u y := fun e => cross ⟨u,ua,y,yb,e⟩
    have tr := only_no_cross ua te ut u_no
    have sub : C.B⊆DistanceTwo G u := by
      intro y yb
      obtain ⟨z,zf,yz⟩ := C.swap.high_port_has_E yb (Bhi y yb)
      have zr := only_no_cross_B yb zf yz (fun v va ed => cross ⟨v,va,y,yb,ed.symm⟩)
      exact C.d2_cross_group ua yb (u_no y yb) (tr ▸ ut) (zr ▸ yz.symm)
    have h := C.local_d2_cap ua C.B_sub_H sub
    omega

private theorem contra_33_two_inner_ordered (A3 : C.A.card=3) (B3 : C.B.card=3)
    (U2 : C.U.card=2) (W2 : C.W.card=2) (I2 : C.I.card=2)
    (Bhi : ∀ x∈C.B,4≤G.degree x) : False := by
  have ia := C.I_in_E_of_three A3
  have ib : C.I⊆C.F := by simpa only [C.swap_I] using C.swap.I_in_E_of_three B3
  have ecap := C.e_cap
  have fcap := C.swap.e_cap
  change C.F.card≤C.W.card at fcap
  have IE : C.I=C.E := eq_of_subset_of_card_le ia (by omega)
  have IF : C.I=C.F := eq_of_subset_of_card_le ib (by omega)
  have no : ∀ x∈C.A,∀ y∈C.B,¬G.Adj x y := fun _ xa _ yb => C.no_cross_of_E_sub_I (by rw [←IE]) xa yb
  obtain ⟨r,ri,t,ti,rt⟩ := one_lt_card.mp (show 1<C.I.card by omega)
  have Is : C.I={r,t} := (eq_of_subset_of_card_le
    (fun z zz => (mem_insert.mp zz).elim (fun h => h.symm ▸ ri) (fun h => (mem_singleton.mp h).symm ▸ ti))
    (by simp [I2,rt])).symm
  have B_hits (y : V) (yb : y∈C.B) : ∃ z∈C.I,G.Adj y z := by
    obtain ⟨z,zf,ed⟩ := C.swap.high_port_has_E yb (Bhi y yb)
    exact ⟨z,IF.symm ▸ zf,ed⟩
  have A_no_both {x : V} (xa : x∈C.A) : ¬(G.Adj x r ∧ G.Adj x t) := by
    rintro ⟨xr,xt⟩
    have sb : C.B⊆DistanceTwo G x := by
      intro y yb
      obtain ⟨z,zi,yz⟩ := B_hits y yb
      rw [Is] at zi
      rcases mem_insert.mp zi with e|e
      · subst z
        exact C.d2_cross_group xa yb (no x xa y yb) xr yz.symm
      · have zt := mem_singleton.mp e
        subst z
        exact C.d2_cross_group xa yb (no x xa y yb) xt yz.symm
    have h := C.local_d2_cap xa C.B_sub_H sb
    omega
  have aclique {x y : V} (xa : x∈C.A) (ya : y∈C.A) (ne : x≠y) : G.Adj x y := by
    have one_direction {u v : V} (ua : u∈C.A) (va : v∈C.A) (uv : u≠v) (hi : 4≤G.degree u) : G.Adj u v := by
      obtain ⟨z,ze,uz⟩ := C.high_port_has_E ua hi
      have zi : z∈C.I := IE.symm ▸ ze
      have req (w : V) (we : w∈C.E) (uw : G.Adj u w) : w=z := by
        have wi : w∈C.I := IE.symm ▸ we
        rw [Is] at wi zi
        rcases mem_insert.mp wi with wr|wt <;> rcases mem_insert.mp zi with zr|zt
        · exact wr.trans zr.symm
        · exact (A_no_both ua ⟨wr ▸ uw,mem_singleton.mp zt ▸ uz⟩).elim
        · exact (A_no_both ua ⟨zr ▸ uz,mem_singleton.mp wt ▸ uw⟩).elim
        · exact (mem_singleton.mp wt).trans (mem_singleton.mp zt).symm
      exact (C.single_inner_peers ua A3 hi req).2 v va uv
    exact (S.degree x y ne).elim (one_direction xa ya ne) (fun hi => (one_direction ya xa ne.symm hi).symm)
  have one_attach : ∃ z∈C.I, (C.A.filter (G.Adj z)).card=1 := by
    let Ar := C.A.filter (G.Adj r)
    let At := C.A.filter (G.Adj t)
    have rpos : 1≤Ar.card := by
      obtain ⟨x,xa,xr⟩ := C.local_a_witness (ia ri)
      exact card_pos.mpr ⟨x,mem_filter.mpr ⟨xa,xr.symm⟩⟩
    have tpos : 1≤At.card := by
      obtain ⟨x,xa,xt⟩ := C.local_a_witness (ia ti)
      exact card_pos.mpr ⟨x,mem_filter.mpr ⟨xa,xt.symm⟩⟩
    have ds : Disjoint Ar At := disjoint_left.mpr (fun x xr xt =>
      A_no_both (mem_filter.mp xr).1 ⟨(mem_filter.mp xr).2.symm,(mem_filter.mp xt).2.symm⟩)
    have sub : Ar∪At⊆C.A := union_subset (filter_subset _ _) (filter_subset _ _)
    have k := card_le_card sub
    rw [card_union_of_disjoint ds] at k
    by_cases h : Ar.card=1
    · exact ⟨r,ri,h⟩
    · exact ⟨t,ti,by change At.card=1; omega⟩
  obtain ⟨z,zi,count⟩ := one_attach
  obtain ⟨x,xeq⟩ := card_eq_one.mp count
  have zx_mem : x∈C.A.filter (G.Adj z) := by rw [xeq]; simp
  obtain ⟨xa,zx⟩ := mem_filter.mp zx_mem
  let Q := insert a (insert b (C.A.erase x))
  have qa : a∉insert b (C.A.erase x) := by
    intro e
    rcases mem_insert.mp e with e|e
    · exact S.ab e
    · exact (S.off (!C.i)).1 (C.A_sub_H (mem_erase.mp e).2)
  have qb : b∉C.A.erase x := fun h => (S.off (!C.i)).2 (C.A_sub_H (mem_erase.mp h).2)
  have qc : Q.card=4 := by
    rw [show Q=insert a (insert b (C.A.erase x)) from rfl,
      card_insert_of_not_mem qa,card_insert_of_not_mem qb,card_erase_of_mem xa,A3]
  have sub : Q⊆DistanceTwo G z := by
    intro u hu
    rcases mem_insert.mp hu with rfl|h
    · exact Sides.mem_d2.mpr (by rw [dist_comm]; exact (C.memE.mp (ia zi)).2)
    rcases mem_insert.mp h with rfl|h
    · exact Sides.mem_d2.mpr (by rw [dist_comm]; exact (C.memF.mp (ib zi)).2)
    obtain ⟨ux,ua⟩ := mem_erase.mp h
    have zad : ¬G.Adj z u := fun e => ux (by
      have uz : u∈C.A.filter (G.Adj z) := mem_filter.mpr ⟨ua,e⟩
      rw [xeq] at uz
      exact mem_singleton.mp uz)
    have zu : z≠u := fun e => C.I_not_A zi (e.symm ▸ ua)
    exact C.d2_of_local_nonedge zu zad zx (aclique xa ua ux.symm)
  have no_extra {u : V} (uq : u∉Q) : u∉DistanceTwo G z := by
    intro ud
    have s : insert u Q⊆DistanceTwo G z :=
      fun v hv => (mem_insert.mp hv).elim (fun e => e.symm ▸ ud) (fun h => sub h)
    have c := card_le_card s
    rw [card_insert_of_not_mem uq,qc] at c
    have h := C.d2_le z
    omega
  have zb_missing : ∃ y∈C.B, ¬G.Adj z y := by
    by_cases e : ∃ y∈C.B,¬G.Adj z y
    · exact e
    exfalso
    have all : C.B⊆DistanceTwo G x := by
      intro y yb
      have zy : G.Adj z y := Classical.byContradiction (fun h => e ⟨y,yb,h⟩)
      exact C.d2_cross_group xa yb (no x xa y yb) zx.symm zy
    have c := C.local_d2_cap xa C.B_sub_H all
    omega
  obtain ⟨y,yb,y_no⟩ := zb_missing
  obtain ⟨w,wi,yw⟩ := B_hits y yb
  have wz : w≠z := fun e => y_no (e ▸ yw.symm)
  have yQ : y∉Q := by
    intro e
    rcases mem_insert.mp e with rfl|e
    · exact (S.off (!C.i)).1 (C.B_sub_H yb)
    rcases mem_insert.mp e with rfl|e
    · exact (S.off (!C.i)).2 (C.B_sub_H yb)
    exact disjoint_left.mp C.dis_AB (mem_erase.mp e).2 yb
  have zy : z≠y := fun e => C.I_not_B zi (e.symm ▸ yb)
  have zw : ¬G.Adj z w := fun e => no_extra yQ (C.d2_of_local_nonedge zy y_no e yw.symm)
  obtain ⟨u,ua,uw⟩ := C.local_a_witness (ia wi)
  have missing : ∃ v∈C.B, ¬G.Adj v w := by
    by_cases h : ∃ v∈C.B,¬G.Adj v w
    · exact h
    exfalso
    have ds : C.B⊆DistanceTwo G u := by
      intro v vb
      have vw : G.Adj v w := Classical.byContradiction (fun no => h ⟨v,vb,no⟩)
      exact C.d2_cross_group ua vb (no u ua v vb) uw vw.symm
    have bound := C.local_d2_cap ua C.B_sub_H ds
    omega
  obtain ⟨v,vb,vw⟩ := missing
  have neq : v≠y := fun e => vw (e.symm ▸ yw)
  have wi_eq : C.I={z,w} := (eq_of_subset_of_card_le
    (fun v hv => (mem_insert.mp hv).elim (fun e => e.symm ▸ zi)
      (fun e => (mem_singleton.mp e).symm ▸ wi)) (by simp [I2,wz.symm])).symm
  have unique {q : V} (qf : q∈C.F) (vq : G.Adj v q) : q=z := by
    have qi : q∈C.I := IF.symm ▸ qf
    rw [wi_eq] at qi
    exact (mem_insert.mp qi).resolve_right (fun e => vw ((mem_singleton.mp e) ▸ vq))
  obtain ⟨vz,vy⟩ := C.swap.single_inner_peers vb B3 (Bhi v vb) (fun _ qf vq => unique qf vq)
  exact no_extra yQ (C.d2_of_local_nonedge zy y_no vz.symm (vy y yb neq))

theorem contra_33 (large : 7≤C.H.card) (A3 : C.A.card=3) (B3 : C.B.card=3) : False := by
  have h := C.count_H
  have ipos : 1≤C.I.card := by omega
  by_cases U1 : C.U.card=1
  · exact C.contra_33_unbalanced A3 B3 U1 ipos
  by_cases W1 : C.W.card=1
  · exact C.swap.contra_33_unbalanced B3 A3 W1 (by simpa only [C.swap_I] using ipos)
  have cp := C.port_K_sum
  have up := C.Upos
  have wp := C.swap.Upos
  change 1≤C.W.card at wp
  have U2 : C.U.card=2 := by omega
  have W2 : C.W.card=2 := by omega
  have cap := C.inner_cap (show 2≤C.A.card by omega)
  by_cases I1 : C.I.card=1
  · rcases C.all_high_group with hi|hi
    · exact C.swap.contra_33_one_inner_ordered B3 A3 W2 U2 (by simpa only [C.swap_I] using I1) hi
    · exact C.contra_33_one_inner_ordered A3 B3 U2 W2 I1 hi
  have I2 : C.I.card=2 := by omega
  rcases C.all_high_group with hi|hi
  · exact C.swap.contra_33_two_inner_ordered B3 A3 W2 U2 (by simpa only [C.swap_I] using I2) hi
  · exact C.contra_33_two_inner_ordered A3 B3 U2 W2 I2 hi

#print axioms contra_33
end Graffiti189LongestPath.TwoCut.FourSideCtx
