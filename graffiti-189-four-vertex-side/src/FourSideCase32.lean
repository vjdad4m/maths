import InnerFour189
namespace Graffiti189LongestPath.TwoCut.FourSideCtx
open SimpleGraph SimpleGraph.Walk Finset
open Graffiti189LongestPath.FourCut.Three
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {a b : V} {S : CutPair G a b} (C : FourSideCtx S)
set_option maxHeartbeats 2100000
set_option linter.unusedSectionVars false

private theorem shell_B_sub_inner (no : ∀ x∈C.A,∀ y∈C.B,¬G.Adj x y) : C.F⊆C.I := by
  intro y yf
  have yh := (C.memF.mp yf).1
  rcases C.classifyH yh with ya|yb|yi
  · obtain ⟨x,xb,xy⟩ := C.swap.local_a_witness yf
    exact (no y ya x xb xy.symm).elim
  · exact (disjoint_left.mp C.swap.E_dis_A yf yb).elim
  · exact yi

private theorem b_distance_ge_three (no : ∀ x∈C.A,∀ y∈C.B,¬G.Adj x y) {x : V} (xa : x∈C.A) :
    3≤G.dist x b := by
  have xh := C.A_sub_H xa
  have na : x≠b := fun e => (S.off (!C.i)).2 (e ▸ xh)
  have nb : ¬G.Adj x b := fun h => C.no_common (C.memA.mp xa).2 h.symm
  have gt := S.con.one_lt_dist_of_ne_of_not_adj na nb
  by_contra! lt
  have d : G.dist b x=2 := by rw [dist_comm]; omega
  have f := C.memF.mpr ⟨xh,d⟩
  exact C.I_not_A (C.shell_B_sub_inner no f) xa

theorem contra_32 (large : 7≤C.H.card) (A3 : C.A.card=3) (B2 : C.B.card=2) : False := by
  have w := C.swap.high_port_implies_foreign_ge_two B2
  change 2≤C.W.card at w
  have bound := C.port_K_sum
  have cnt := C.count_H
  have ia := C.I_in_E_of_three A3
  have ic := card_le_card ia
  have ecap := C.e_cap
  have I2 : C.I.card=2 := by omega
  have U2 : C.U.card=2 := by omega
  have W2 : C.W.card=2 := by omega
  have E2 : C.E.card=2 := by omega
  have IE : C.I=C.E := eq_of_subset_of_card_le ia (by omega)
  have no : ∀ x∈C.A,∀ y∈C.B,¬G.Adj x y :=
    fun x hx y hy => C.no_cross_of_E_sub_I (by rw [←IE]) hx hy
  have fsub := C.shell_B_sub_inner no
  obtain ⟨y,yb,yhigh⟩ := C.high_of_two (show 2≤C.B.card by omega)
  have dy := C.swap.degree_A yb
  change G.degree y≤C.B.card+C.F.card at dy
  have fcap := C.swap.e_cap
  change C.F.card≤C.W.card at fcap
  have F2 : C.F.card=2 := by omega
  have FI := eq_of_subset_of_card_le fsub (by omega)
  have all_y {x : V} (xb : x∈C.B) (high : 4≤G.degree x) {z : V} (zi : z∈C.I) : G.Adj x z :=
    C.swap.tight_joins_E xb (show z∈C.F from FI.symm ▸ zi) high (by change C.B.card+C.F.card=4; omega)
  let L := C.A.filter (fun x => ∃ r∈C.I,G.Adj x r)
  have Ld : L⊆DistanceTwo G y := by
    intro x lx
    obtain ⟨xa,r,ri,xr⟩ := mem_filter.mp lx
    exact C.swap.d2_cross_group yb xa (fun e => no x xa y yb e.symm) (all_y yb yhigh ri) xr.symm
  have lc := C.swap.local_d2_cap yb ((filter_subset _ _).trans C.A_sub_H) Ld
  change L.card+C.W.card≤4 at lc
  have ex : ∃ z∈C.A,z∉L := by
    by_cases ex : ∃ z∈C.A,z∉L
    · exact ex
    exfalso
    have sub : C.A⊆L := fun x xa => Classical.byContradiction (fun h => ex ⟨x,xa,h⟩)
    have d := card_le_card sub
    omega
  obtain ⟨z,za,nL⟩ := ex
  have z_no_I : ∀ t∈C.I, ¬G.Adj z t := fun t ti e => nL (mem_filter.mpr ⟨za,t,ti,e⟩)
  have zlow : ¬4≤G.degree z := by
    intro d
    obtain ⟨r,re,zr⟩ := C.high_port_has_E za d
    exact z_no_I r (IE.symm ▸ re) zr
  have Bhigh (x : V) (xb : x∈C.B) : 4≤G.degree x :=
    (S.degree x z (fun h => disjoint_left.mp C.dis_AB za (h ▸ xb))).resolve_right zlow
  have Ihigh (x : V) (xi : x∈C.I) : 4≤G.degree x :=
    (S.degree x z (fun h => C.I_not_A xi (h.symm ▸ za))).resolve_right zlow
  have all_x {x : V} (xa : x∈C.A) (high : 4≤G.degree x) : ∀ t∈C.I,G.Adj x t := by
    obtain ⟨r,re,xr⟩ := C.high_port_has_E xa high
    have ri : r∈C.I := IE.symm ▸ re
    intro t ti
    by_cases xt : G.Adj x t
    · exact xt
    exfalso
    have rt : r≠t := fun e => xt (e ▸ xr)
    have zx : z≠x := fun e => zlow (e.symm ▸ high)
    have tr : G.Adj t r := by
      by_cases tr : G.Adj t r
      · exact tr
      exfalso
      have sub : G.neighborFinset t⊆C.B∪((C.A.erase z).erase x) := by
        intro u hu
        have tu := (mem_neighborFinset G t u).mp hu
        rcases C.classifyH (C.I_neighbors_H ti tu) with ua|ub|ui
        · have uz : u≠z := fun e => z_no_I t ti (e ▸ tu.symm)
          have ux : u≠x := fun e => xt (e ▸ tu.symm)
          exact mem_union.mpr (Or.inr (mem_erase.mpr ⟨ux,mem_erase.mpr ⟨uz,ua⟩⟩))
        · exact mem_union.mpr (Or.inl ub)
        · have eq : C.I={r,t} := eq_of_subset_of_card_le
            (by intro u hu; rcases mem_insert.mp hu with rfl|h; exact ri; exact (mem_singleton.mp h).symm ▸ ti)
            (by simp [I2,rt]) |>.symm
          rw [eq] at ui
          rcases mem_insert.mp ui with ur|ut
          · exact (tr (ur ▸ tu)).elim
          · exact (tu.ne (mem_singleton.mp ut).symm).elim
      have ca := card_le_card sub
      rw [card_neighborFinset_eq_degree] at ca
      have cb := card_union_le C.B ((C.A.erase z).erase x)
      rw [card_erase_of_mem (mem_erase.mpr ⟨zx.symm,xa⟩),card_erase_of_mem za,A3,B2] at cb
      have hi := Ihigh t ti
      omega
    have fb : C.B⊆DistanceTwo G x := by
      intro u ub
      exact C.d2_cross_group xa ub (no x xa u ub) xr (all_y ub (Bhigh u ub) ri).symm
    have xnt : x≠t := fun e => C.I_not_A ti (e ▸ xa)
    exact C.no_extra_local xa U2 B2 C.B_sub_H fb (C.I_sub_H ti) (C.I_not_B ti)
      (C.d2_of_local_nonedge xnt xt xr tr.symm)
  have zneigh : G.neighborFinset z⊆insert a (C.A.erase z) := by
    intro u hu
    rcases mem_insert.mp (C.local_A_neighbor_sub za hu) with rfl|h
    · exact mem_insert_self _ _
    rcases mem_union.mp h with h|h
    · exact mem_insert_of_mem h
    exact (z_no_I u (IE.symm ▸ h) ((mem_neighborFinset G z u).mp hu)).elim
  have za_peers : ∃ x∈C.A, G.Adj z x := by
    by_cases hit : ∃ x∈C.A,G.Adj z x
    · exact hit
    exfalso
    have only : G.neighborFinset z⊆{a} := by
      intro u hu
      rcases mem_insert.mp (zneigh hu) with rfl|ua
      · simp
      · exact (hit ⟨u,(mem_erase.mp ua).2,(mem_neighborFinset G z u).mp hu⟩).elim
    have cb := card_le_card only
    rw [card_neighborFinset_eq_degree,card_singleton] at cb
    have h := C.min2 z
    omega
  obtain ⟨x,xa,zx⟩ := za_peers
  have xhi := (S.degree x z zx.ne.symm).resolve_right zlow
  have dI : C.I⊆DistanceTwo G z := by
    intro t ti
    have zt : z≠t := fun e => C.I_not_A ti (e ▸ za)
    exact C.d2_of_local_nonedge zt (z_no_I t ti) zx (all_x xa xhi t ti)
  have capset : C.I∪C.U⊆DistanceTwo G z := union_subset dI (fun _ hu => C.foreign_U_d2 za hu)
  have ds : Disjoint C.I C.U := C.dis_KH.symm.mono C.I_sub_H (fun _ hu => (C.memU.mp hu).1)
  have big := card_le_card capset
  rw [card_union_of_disjoint ds,I2,U2] at big
  have far : 4≤G.dist z b := by
    apply Nat.le_of_not_gt
    intro small
    obtain ⟨p,pl⟩ := S.con.exists_walk_length_eq_dist z b
    cases p with
    | nil => exact (S.off (!C.i)).2 (C.A_sub_H za)
    | @cons _ t _ zt q =>
      have le := G.dist_le q
      simp at pl
      have tset := zneigh ((mem_neighborFinset G z t).mpr zt)
      rcases mem_insert.mp tset with rfl|tset
      · have d := C.cut_dist
        omega
      · have d := C.b_distance_ge_three no (mem_erase.mp tset).2
        omega
  have ce := distanceTwo_add_two_le_even_of_far S.con far
  have en := S.even z
  omega

#print axioms contra_32
end Graffiti189LongestPath.TwoCut.FourSideCtx
