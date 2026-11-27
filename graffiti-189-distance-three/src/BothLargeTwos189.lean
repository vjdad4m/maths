import BothLargeCases189
namespace Graffiti189LongestPath.TwoCut.DistThreeCtx
open SimpleGraph SimpleGraph.Walk Finset
open Graffiti189LongestPath.FourCut.Three
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {a b : V} {S : CutPair G a b} (C : DistThreeCtx S)
set_option maxHeartbeats 2200000
set_option linter.unusedSectionVars false

private theorem no_bridge_if_complete_groups (A2 : C.A.card=2) (B2 : C.B.card=2)
    (Eeq : C.E=C.B) (Feq : C.F=C.A) (large : 5≤C.H.card) : False := by
  obtain ⟨x,xa⟩ := card_pos.mp C.Apos
  let P := C.A∪C.B
  have psub : P⊆C.H := union_subset C.A_sub_H C.B_sub_H
  have closed (y z : V) (yp : y∈P) (zh : z∈C.H) (yz : G.Adj y z) : z∈P := by
    have ha : z≠a := (C.H_abs zh).1
    have hb : z≠b := (C.H_abs zh).2
    rcases mem_union.mp yp with ya|yb
    · have q := C.local_A_neighbor_sub ya ((mem_neighborFinset G y z).mpr yz)
      simp only [mem_insert,ha,false_or,mem_union,mem_erase,Eeq] at q
      exact mem_union.mpr (q.imp And.right id)
    · have q := C.swap.local_A_neighbor_sub yb ((mem_neighborFinset G y z).mpr yz)
      change z∈insert b (C.B.erase y∪C.F) at q
      simp only [mem_insert,hb,false_or,mem_union,mem_erase,Feq] at q
      exact mem_union.mpr (q.symm.imp id And.right)
  have Hsub : C.H⊆P := by
    intro z zh
    obtain ⟨q,qs⟩ := C.joined_H (C.A_sub_H xa) zh
    have go {u v : V} (q : G.Walk u v) (qs : ∀ w∈q.support,w∈C.H) (up : u∈P) : v∈P := by
      induction q with
      | nil => exact up
      | @cons u w v e q ih =>
        exact ih (fun y hy => qs y (by simp [hy])) (closed u w up (qs w (by simp)) e)
    exact go q qs (mem_union.mpr (Or.inl xa))
  have c := card_le_card Hsub
  change C.H.card≤(C.A∪C.B).card at c
  rw [card_union_of_disjoint C.dis_AB,A2,B2] at c
  omega

private theorem bridge_to_B_forces_E (B2 : C.B.card=2) (E2 : C.E.card=2) (F2 : C.F.card=2)
    (Bhigh : ∀ y∈C.B,4≤G.degree y)
    {x y : V} (xa : x∈C.A) (yb : y∈C.B) (xy : G.Adj x y) : C.E=C.B := by
  have xf := C.swap.local_a_d2 yb (C.A_sub_H xa) (fun xb => disjoint_left.mp C.dis_AB xa xb) xy.symm
  have sub : C.B⊆C.E := by
    intro z zb
    have zx := C.swap.tight_joins_E zb xf (Bhigh z zb) (by change C.B.card+C.F.card=4; omega)
    exact C.local_a_d2 xa (C.B_sub_H zb) (fun za => disjoint_left.mp C.dis_AB za zb) zx.symm
  exact (eq_of_subset_of_card_le sub (by omega)).symm

theorem only_low_side_bridges_22 (lg : 5≤C.H.card) (A2 : C.A.card=2) (B2 : C.B.card=2)
    (E2 : C.E.card=2) (F2 : C.F.card=2)
    (Ahi : ∀ x∈C.A,4≤G.degree x) (Bhi : ∀ y∈C.B,4≤G.degree y) : ¬C.Bridge := by
  rintro ⟨x,xa,y,yb,xy⟩
  have e := C.bridge_to_B_forces_E B2 E2 F2 Bhi xa yb xy
  have f := C.swap.bridge_to_B_forces_E A2 F2 E2 Ahi yb xa xy.symm
  exact C.no_bridge_if_complete_groups A2 B2 e f lg

private theorem drop_low_from_bridge_or_no_low {x y : V} (xa : x∈C.A) (yb : y∈C.B)
    (xy : G.Adj x y) (A2 : C.A.card=2) (B2 : C.B.card=2) (E2 : C.E.card=2) (F2 : C.F.card=2)
    (lg : 5≤C.H.card) (lk : 5≤C.K.card)
    (U2 : C.U.card=2) (W2 : C.W.card=2)
    (KE2 : C.other.E.card=2) (KF2 : C.other.F.card=2)
    (Bhi : ∀ z∈C.B,4≤G.degree z) : False := by
  have e := C.bridge_to_B_forces_E B2 E2 F2 Bhi xa yb xy
  by_cases alld : ∀ z∈C.A,4≤G.degree z
  · exact C.only_low_side_bridges_22 lg A2 B2 E2 F2 alld Bhi ⟨x,xa,y,yb,xy⟩
  obtain ⟨l,lh⟩ := not_forall.mp alld
  have la : l∈C.A := Classical.byContradiction (fun e => lh (fun x => (e x).elim))
  have low : ¬4≤G.degree l := fun hi => lh (fun _ => hi)
  obtain ⟨t,ta,thi⟩ := C.high_of_two (show 2≤C.A.card by omega)
  have lt : l≠t := fun eq => low (eq.symm ▸ thi)
  have tf_all (z : V) (zb : z∈C.B) : G.Adj t z :=
    C.tight_joins_E ta (e.symm ▸ zb) thi (by omega)
  have lno (z : V) (zb : z∈C.B) : ¬G.Adj l z := by
    intro lz
    have lF := C.swap.local_a_d2 zb (C.A_sub_H la) (fun lb => disjoint_left.mp C.dis_AB la lb) lz.symm
    have tF := C.swap.local_a_d2 yb (C.A_sub_H ta) (fun tb => disjoint_left.mp C.dis_AB ta tb) (tf_all y yb).symm
    have sub : {l,t}⊆C.F := fun z hz => (mem_insert.mp hz).elim (fun eq => eq.symm ▸ lF)
      (fun ez => (mem_singleton.mp ez).symm ▸ tF)
    have eq : C.F={l,t} := (eq_of_subset_of_card_le sub (by simp [F2,lt])).symm
    have ab : {l,t}⊆C.A := fun z hz => (mem_insert.mp hz).elim (fun eq => eq.symm ▸ la)
      (fun ez => (mem_singleton.mp ez).symm ▸ ta)
    have eq' : C.A={l,t} := (eq_of_subset_of_card_le ab (by simp [A2,lt])).symm
    exact C.no_bridge_if_complete_groups A2 B2 e (eq.trans eq'.symm) lg
  have Q : G.neighborFinset l⊆{a,t} := by
    intro z hz
    rcases mem_insert.mp (C.local_A_neighbor_sub la hz) with za|res
    · exact mem_insert.mpr (Or.inl za)
    rcases mem_union.mp res with za|ze
    · have za' := (mem_erase.mp za).2
      have ac : C.A={l,t} := (eq_of_subset_of_card_le
        (fun z hz => (mem_insert.mp hz).elim (fun eq => eq.symm ▸ la)
          (fun ez => (mem_singleton.mp ez).symm ▸ ta)) (by simp [A2,lt])).symm
      rw [ac] at za'
      exact mem_insert.mpr (Or.inr ((mem_insert.mp za').resolve_left (mem_erase.mp za).1))
    · exact (lno z (e ▸ ze) ((mem_neighborFinset G l z).mp hz)).elim
  have lt_adj : G.Adj l t := by
    by_cases edge : G.Adj l t
    · exact edge
    exfalso
    have sub : G.neighborFinset l⊆{a} := by
      intro z hz
      rcases mem_insert.mp (Q hz) with he|he
      · exact mem_singleton.mpr he
      · exact (edge ((mem_singleton.mp he) ▸ (mem_neighborFinset G l z).mp hz)).elim
    have c := card_le_card sub
    rw [card_neighborFinset_eq_degree,card_singleton] at c
    have m := C.min2 l
    omega
  have Bdis : C.B⊆DistanceTwo G l := fun z zb =>
    C.d2_cross_group la zb (lno z zb) lt_adj (tf_all z zb)
  have super : 4≤(DistanceTwo G l).card := by
    have sub : C.B∪C.U⊆DistanceTwo G l :=
      union_subset Bdis (fun _ z => C.foreign_U_d2 la z)
    have d := C.dis_KH.symm.mono C.B_sub_H (fun _ h => (C.memU.mp h).1)
    have c := card_le_card sub
    rw [card_union_of_disjoint d,B2,U2] at c
    exact c
  have highK {z : V} (zk : z∈C.K) : 4≤G.degree z :=
    (S.degree l z (fun e => disjoint_left.mp C.dis_KH zk (e ▸ C.A_sub_H la))).resolve_left low
  have kno := C.other.only_low_side_bridges_22 lk U2 W2 KE2 KF2
    (fun _ e => highK (C.other.A_sub_H e)) (fun _ e => highK (C.other.B_sub_H e))
  obtain ⟨z,zw⟩ := card_pos.mp C.swap.Upos
  have dz := C.other.swap.port_b_dist_ge_three zw
    (fun w wa wz => kno ⟨w,wa,z,zw,wz.symm⟩)
  have la1 : G.dist l a=1 := dist_eq_one_iff_adj.mpr (C.memA.mp la).2.symm
  have lb3 := C.port_b_dist_ge_three la lno
  have bz1 : G.dist b z=1 := dist_eq_one_iff_adj.mpr (C.memW.mp zw).2
  have eq := S.cross_distance_eq C.different.symm (C.A_sub_H la) (C.memW.mp zw).1
  rw [dist_comm] at dz
  have contradiction := distanceTwo_add_two_le_even_of_far S.con (show 4≤G.dist l z by omega)
  have bound := S.even l
  omega

theorem impossible_22_22 (A2 : C.A.card=2) (U2 : C.U.card=2)
    (B2 : C.B.card=2) (W2 : C.W.card=2) (lg : 5≤C.H.card) (lk : 5≤C.K.card) : False := by
  have cut (D : DistThreeCtx S) (A2 : D.A.card=2) (U2 : D.U.card=2)
      (B2 : D.B.card=2) (W2 : D.W.card=2) (lg : 5≤D.H.card) (lk : 5≤D.K.card)
      (bridge : D.Bridge) : False := by
    obtain ⟨E2,KE2⟩ := D.exact_if_twos A2 U2
    obtain ⟨F2,KF2⟩ := D.swap.exact_if_twos B2 W2
    obtain ⟨x,xa,y,yb,xy⟩ := bridge
    rcases D.all_high_group with allA|allB
    · exact D.swap.drop_low_from_bridge_or_no_low yb xa xy.symm B2 A2 F2 E2 lg lk W2 U2 KF2 KE2 allA
    · exact D.drop_low_from_bridge_or_no_low xa yb xy A2 B2 E2 F2 lg lk U2 W2 KE2 KF2 allB
  exact C.bridge_either.elim (cut C A2 U2 B2 W2 lg lk) (cut C.other U2 A2 W2 B2 lk lg)

#print axioms impossible_22_22
end Graffiti189LongestPath.TwoCut.DistThreeCtx
