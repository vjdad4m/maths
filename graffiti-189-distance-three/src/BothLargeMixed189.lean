import BothLargeTwos189
namespace Graffiti189LongestPath.TwoCut.DistThreeCtx
open SimpleGraph SimpleGraph.Walk Finset
open Graffiti189LongestPath.FourCut.Three
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {a b : V} {S : CutPair G a b} (C : DistThreeCtx S)
set_option maxHeartbeats 2600000
set_option linter.unusedSectionVars false

private theorem no_finished_local {x : V} (xa : x∈C.A) {Q : Finset V}
    (qH : Q⊆C.H) (qd : Q⊆DistanceTwo G x) (full : Q.card+C.U.card=4)
    {z : V} (zh : z∈C.H) (zn : z∉Q) : z∉DistanceTwo G x := by
  intro d
  have c := C.local_d2_cap xa
    (show insert z Q⊆C.H from fun t ht => (mem_insert.mp ht).elim (fun e => e.symm ▸ zh) (fun h => qH h))
    (show insert z Q⊆DistanceTwo G x from fun t ht => (mem_insert.mp ht).elim (fun e => e.symm ▸ d) (fun h => qd h))
  rw [card_insert_of_not_mem zn] at c
  omega

private theorem mixed_bridge_impossible (A2 : C.A.card=2) (U3 : C.U.card=3)
    (B2 : C.B.card=2) (W2 : C.W.card=2) (lg : 5≤C.H.card) (bridge : C.Bridge) : False := by
  obtain ⟨x,xa,y,yb,xy⟩ := bridge
  have all := C.bridge_propagates xa yb xy U3 (by omega)
  have F2 := (C.swap.exact_if_twos B2 W2).1
  change C.F.card=2 at F2
  have E := C.shell_eq_of_universal xa (all x xa)
  have cnt := card_sdiff_add_card_eq_card C.A_sub_H
  rw [←E] at cnt
  have es := C.shell_sum
  have op := C.other.E_pos
  have h5 : C.H.card=5 := by omega
  have I1 : C.I.card=1 := by
    have cnt := C.count_H
    omega
  obtain ⟨z,zi⟩ := card_pos.mp (show 0<C.I.card by omega)
  have zh := C.I_sub_H zi
  have zA := (C.memI.mp zi).2.1
  have zB := (C.memI.mp zi).2.2
  have aF : C.A⊆C.F := by
    intro w wa
    have wy : w≠y := fun e => disjoint_left.mp C.dis_AB wa (e.symm ▸ yb)
    have adj := (all w wa y (C.B_sub_H yb)).resolve_left wy
    exact C.swap.local_a_d2 yb (C.A_sub_H wa) (fun wb => disjoint_left.mp C.dis_AB wa wb) adj.symm
  have Feq : C.A=C.F := eq_of_subset_of_card_le aF (by omega)
  have no : z∉C.F := fun e => zA (C.memA.mp (Feq.symm ▸ e)).2
  have zx : z≠x := fun e => zA (e.symm ▸ (C.memA.mp xa).2)
  have xz := (all x xa z zh).resolve_left zx.symm
  have da : G.dist z a=2 := Sides.dist_two S.con (C.H_abs zh).1 (fun e => zA e.symm)
    xz.symm (C.memA.mp xa).2.symm
  have db : G.dist z b=3 := by
    have q := G.dist_le (Walk.cons xz.symm (Walk.cons xy (Walk.cons (C.memB.mp yb).2.symm Walk.nil)))
    simp at q
    have lb := S.con.one_lt_dist_of_ne_of_not_adj (C.H_abs zh).2 (fun e => zB e.symm)
    have ne : G.dist z b≠2 := fun e => no (C.memF.mpr ⟨zh,by rwa [dist_comm]⟩)
    omega
  have dB : C.B⊆DistanceTwo G z := by
    intro w wb
    have zw : z≠w := fun e => zB (e.symm ▸ (C.memB.mp wb).2)
    have nx : ¬G.Adj z w := fun e => no (C.swap.local_a_d2 wb zh
      (fun hz => zB (C.memB.mp hz).2) e.symm)
    have xw : x≠w := fun e => disjoint_left.mp C.dis_AB xa (e.symm ▸ wb)
    exact Sides.mem_d2.mpr (Sides.dist_two S.con zw nx xz.symm ((all x xa w (C.B_sub_H wb)).resolve_left xw))
  have dbig : 3≤(DistanceTwo G z).card := by
    have sub : insert a C.B⊆DistanceTwo G z := by
      intro w ww
      exact (mem_insert.mp ww).elim (fun e => e.symm ▸ Sides.mem_d2.mpr da) (fun e => dB e)
    have cap := card_le_card sub
    rw [card_insert_of_not_mem (fun h => (S.off C.j).1 (C.B_sub_H h)),B2] at cap
    exact cap
  have sd : C.W⊆Shell G z 4 := by
    intro w ww
    obtain ⟨wk,bw⟩ := C.memW.mp ww
    have eq := S.cross_distance_eq C.different.symm zh wk
    have bw1 := dist_eq_one_iff_adj.mpr bw
    have aw2 := S.con.one_lt_dist_of_ne_of_not_adj
      (C.other.H_abs wk).1.symm (fun e => C.no_common e bw)
    exact mem_shell.mpr (by omega)
  have cap := card_le_card sd
  have bg := shell_two_four_le_of_even (x:=z) (d:=4) (S.even z)
  have eq : Shell G z 2=DistanceTwo G z := by ext w; simp [Shell,DistanceTwo]
  rw [eq] at bg
  omega

private theorem mixed_no_bridge_impossible (A2 : C.A.card=2) (U3 : C.U.card=3)
    (B2 : C.B.card=2) (W2 : C.W.card=2) (no : ¬C.Bridge) : False := by
  let nB (x y : V) (xa : x∈C.A) (yb : y∈C.B) : ¬G.Adj x y := fun e => no ⟨x,xa,y,yb,e⟩
  obtain ⟨x,xa,xhi⟩ := C.high_of_two (show 2≤C.A.card by omega)
  have wE := card_le_card (C.foreign_opp_near xa U3 (fun y yb => nB x y xa yb))
  have quo := C.quota (show 2≤C.A.card by omega)
  have sum := C.shell_sum
  have E2 : C.E.card=2 := by omega
  have F2 := (C.swap.exact_if_twos B2 W2).1
  change C.F.card=2 at F2
  have es := C.shell_sub_inner_no_bridge no
  have fs : C.F⊆C.I := by
    have h := C.swap.shell_sub_inner_no_bridge (fun e => no (C.bridge_swap.mp e))
    simpa only [C.swap_I] using h
  have xE {z : V} (ze : z∈C.E) : G.Adj x z := C.tight_joins_E xa ze xhi (by omega)
  obtain ⟨r,re,rf,xr⟩ := C.B_inter_E_of_saturated_no_bridge U3 no xa
  obtain ⟨y,yb,yhi⟩ := C.high_of_two (show 2≤C.B.card by omega)
  have yF {z : V} (zf : z∈C.F) : G.Adj y z :=
    C.swap.tight_joins_E yb zf yhi (by change C.B.card+C.F.card=4; omega)
  have yd : y∈DistanceTwo G x := C.d2_cross_group xa yb (nB x y xa yb) xr (yF rf).symm
  have yD : ({y}:Finset V)⊆DistanceTwo G x := fun w h => (mem_singleton.mp h).symm ▸ yd
  have yH : ({y}:Finset V)⊆C.H := fun w h => (mem_singleton.mp h).symm ▸ C.B_sub_H yb
  have ycap {z : V} (zh : z∈C.H) (zn : z∉({y}:Finset V)) : z∉DistanceTwo G x :=
    C.no_finished_local xa yH yD (by simp [U3]) zh zn
  obtain ⟨l,lb,ly⟩ : ∃ l∈C.B,l≠y := by
    have c := card_erase_of_mem yb
    obtain ⟨u,hu⟩ := card_pos.mp (show 0<(C.B.erase y).card by omega)
    exact ⟨u,(mem_erase.mp hu).2,(mem_erase.mp hu).1⟩
  have llo : ¬4≤G.degree l := by
    intro lhi
    have lr := C.swap.tight_joins_E lb rf lhi (by change C.B.card+C.F.card=4; omega)
    exact ycap (C.B_sub_H lb) (by simpa using ly)
      (C.d2_cross_group xa lb (nB x l xa lb) xr lr.symm)
  have Ahi {z : V} (za : z∈C.A) : 4≤G.degree z :=
    (S.degree z l (fun e => disjoint_left.mp C.dis_AB za (e.symm ▸ lb))).resolve_right llo
  have yd2 : C.A⊆DistanceTwo G y := by
    intro z za
    have zr := C.tight_joins_E za re (Ahi za) (by omega)
    exact C.swap.d2_cross_group yb za (fun e => nB z y za yb e.symm) (yF rf) zr.symm
  have yfull {z : V} (zh : z∈C.H) (zn : z∉C.A) : z∉DistanceTwo G y :=
    C.swap.no_finished_local yb C.A_sub_H yd2 (by change C.A.card+C.W.card=4; omega) zh zn
  by_cases eq : C.E=C.F
  · have lF (z : V) (zf : z∈C.F) : ¬G.Adj l z := by
      intro lz
      exact ycap (C.B_sub_H lb) (by simpa using ly)
        (C.d2_cross_group xa lb (nB x l xa lb) (xE (eq.symm ▸ zf)) lz.symm)
    have LN : G.neighborFinset l⊆{b,y} := by
      intro z hz
      rcases mem_insert.mp (C.swap.local_A_neighbor_sub lb hz) with eb|h
      · exact mem_insert.mpr (Or.inl eb)
      rcases mem_union.mp h with h|h
      · have B := (eq_of_subset_of_card_le
          (show ({l,y}:Finset V)⊆C.B from fun _ hm => (mem_insert.mp hm).elim
            (fun e => e.symm ▸ lb) (fun e => (mem_singleton.mp e).symm ▸ yb))
          (by simp [B2,ly])).symm
        have zz : z∈C.B := (mem_erase.mp h).2
        rw [B] at zz
        exact mem_insert.mpr (Or.inr ((mem_insert.mp zz).resolve_left (mem_erase.mp h).1))
      · exact (lF z h ((mem_neighborFinset G l z).mp hz)).elim
    have edge : G.Adj l y := by
      by_cases e : G.Adj l y
      · exact e
      exfalso
      have d : G.neighborFinset l⊆{b} := by
        intro z hz
        rcases mem_insert.mp (LN hz) with eq|eq
        · exact mem_singleton.mpr eq
        · exact (e ((mem_singleton.mp eq) ▸ (mem_neighborFinset G l z).mp hz)).elim
      have c := card_le_card d
      rw [card_neighborFinset_eq_degree,card_singleton] at c
      have m := C.min2 l
      omega
    have cap : 4≤(DistanceTwo G l).card := by
      have sub : C.F⊆DistanceTwo G l := by
        intro z zf
        have lz : l≠z := fun e => (C.memI.mp (fs zf)).2.2 (e ▸ (C.memB.mp lb).2)
        exact Sides.mem_d2.mpr (Sides.dist_two S.con lz (lF z zf) edge (yF zf))
      have union : C.F∪C.W⊆DistanceTwo G l :=
        union_subset sub (fun _ e => C.swap.foreign_U_d2 lb e)
      have d : Disjoint C.F C.W :=
        C.dis_KH.symm.mono (fun _ e => (C.memF.mp e).1) (fun _ e => (C.memW.mp e).1)
      have c := card_le_card union
      rw [card_union_of_disjoint d,F2,W2] at c
      exact c
    have far : 4≤G.dist l a := by
      apply Nat.le_of_not_gt
      intro sh
      obtain ⟨w,wl⟩ := S.con.exists_walk_length_eq_dist l a
      cases w with
      | nil => exact (C.H_abs (C.B_sub_H lb)).1 rfl
      | @cons _ z _ lz w =>
        have d := G.dist_le w
        simp at wl
        rcases mem_insert.mp (LN ((mem_neighborFinset G l z).mpr lz)) with e|e
        · have e' := C.cut_dist
          have dz : 3≤G.dist z a := by
            rw [e,dist_comm]
            omega
          omega
        · have e' := C.swap.port_b_dist_ge_three yb (fun u ua => fun e => nB u y ua yb e.symm)
          have dz : 3≤G.dist z a := by
            rw [mem_singleton.mp e]
            exact e'
          omega
    have eb := distanceTwo_add_two_le_even_of_far S.con far
    have ee := S.even l
    omega
  obtain ⟨t,tf,te⟩ : ∃ t∈C.F,t∉C.E := by
    by_cases h : ∃ t∈C.F,t∉C.E
    · exact h
    exfalso
    have sub : C.F⊆C.E := fun t tf => Classical.byContradiction (fun tn => h ⟨t,tf,tn⟩)
    exact eq ((eq_of_subset_of_card_le sub (by omega)).symm)
  have ti := fs tf
  have tnA (z : V) (za : z∈C.A) : ¬G.Adj t z := fun tz =>
    te (C.local_a_d2 za (C.I_sub_H ti) (fun ta => (C.memI.mp ti).2.1 (C.memA.mp ta).2) tz.symm)
  have nE (z : V) (ze : z∈C.E) : ¬G.Adj t z := by
    intro tz
    have no_xt : ¬G.Adj x t := fun e => tnA x xa e.symm
    have xt : x≠t := fun e => (C.memI.mp ti).2.1 (e ▸ (C.memA.mp xa).2)
    have nt : t∉({y}:Finset V) := by
      intro h
      exact (C.memI.mp ti).2.2 ((mem_singleton.mp h).symm ▸ (C.memB.mp yb).2)
    exact ycap (C.I_sub_H ti) nt (Sides.mem_d2.mpr (Sides.dist_two S.con xt no_xt (xE ze) tz.symm))
  have nF (z : V) (zi : z∈C.I) (zf : z∉C.F) : ¬G.Adj t z := by
    intro tz
    have no_yz : ¬G.Adj y z := fun e =>
      zf (C.swap.local_a_d2 yb (C.I_sub_H zi)
        (fun zb => (C.memI.mp zi).2.2 (C.memB.mp zb).2) e)
    have yz : y≠z := fun e => (C.memI.mp zi).2.2 (e ▸ (C.memB.mp yb).2)
    have za : z∉C.A := fun za => (C.memI.mp zi).2.1 (C.memA.mp za).2
    exact yfull (C.I_sub_H zi) za (Sides.mem_d2.mpr (Sides.dist_two S.con yz no_yz (yF tf) tz))
  have tr : t≠r := fun e => te (e.symm ▸ re)
  have Feq : C.F={t,r} := (eq_of_subset_of_card_le
    (fun z zh => (mem_insert.mp zh).elim (fun e => e.symm ▸ tf) (fun e => (mem_singleton.mp e).symm ▸ rf))
    (by simp [F2,tr])).symm
  have nb : G.neighborFinset t⊆C.B := by
    intro z hz
    have tz := (mem_neighborFinset G t z).mp hz
    have zh : z∈C.H := by
      have th := C.I_sub_H ti
      rcases S.closed C.j t th z tz with rfl|rfl|zh
      · exact ((C.memI.mp ti).2.1 tz.symm).elim
      · exact ((C.memI.mp ti).2.2 tz.symm).elim
      · exact zh
    rcases C.split_H zh with za|zb|zi
    · exact (tnA z za tz).elim
    · exact zb
    by_cases zf : z∈C.F
    · rw [Feq] at zf
      rcases mem_insert.mp zf with e|e
      · exact (tz.ne e.symm).elim
      · exact (nE r re ((mem_singleton.mp e) ▸ tz)).elim
    · exact (nF z zi zf tz).elim
  have c := card_le_card nb
  rw [card_neighborFinset_eq_degree,B2] at c
  have lnt : l≠t := fun e => (C.memI.mp ti).2.2 (e ▸ (C.memB.mp lb).2)
  exact (S.degree l t lnt).elim llo (by omega)

theorem impossible_23_22 (A2 : C.A.card=2) (U3 : C.U.card=3)
    (B2 : C.B.card=2) (W2 : C.W.card=2) (lg : 5≤C.H.card) : False := by
  by_cases bridge : C.Bridge
  · exact C.mixed_bridge_impossible A2 U3 B2 W2 lg bridge
  · exact C.mixed_no_bridge_impossible A2 U3 B2 W2 bridge

#print axioms impossible_23_22
end Graffiti189LongestPath.TwoCut.DistThreeCtx
