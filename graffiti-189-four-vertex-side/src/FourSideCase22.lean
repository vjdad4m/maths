import InnerFour189
namespace Graffiti189LongestPath.TwoCut.FourSideCtx
open SimpleGraph SimpleGraph.Walk Finset
open Graffiti189LongestPath.FourCut.Three
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {a b : V} {S : CutPair G a b} (C : FourSideCtx S)
set_option maxHeartbeats 1700000
set_option linter.unusedSectionVars false

private theorem missing_of_equal_shells (A2 : C.A.card=2) (B2 : C.B.card=2)
    (U2 : C.U.card=2) (I3 : C.I.card=3)
    (E2 : C.E.card=2) (Esub : C.E⊆C.I) (eq : C.E=C.F) : False := by
  have n : 0<(C.I\C.E).card := by
    have h := card_sdiff_add_card_eq_card Esub
    omega
  obtain ⟨z,hz⟩ := card_pos.mp n
  obtain ⟨zi,ze⟩ := mem_sdiff.mp hz
  have zf : z∉C.F := by rwa [←eq]
  have low : ¬4≤G.degree z := by
    have le := C.inner_degree_bound_of_nonnear zi ze zf
    omega
  have deg := C.min2 z
  obtain ⟨t,ht⟩ := card_pos.mp (show 0<(G.neighborFinset z).card by
    rw [card_neighborFinset_eq_degree]; omega)
  have zt := (mem_neighborFinset G z t).mp ht
  have ti : t∈C.I := by
    rcases C.classifyH (C.I_neighbors_H zi zt) with ta|tb|ti
    · exact (ze (C.local_a_d2 ta (C.I_sub_H zi) (C.I_not_A zi) zt.symm)).elim
    · exact (zf (C.swap.local_a_d2 tb (C.I_sub_H zi) (C.I_not_B zi) zt.symm)).elim
    · exact ti
  have cover : insert z C.E=C.I := eq_of_subset_of_card_le
    (fun w hw => (mem_insert.mp hw).elim (fun e => e.symm ▸ zi) (fun e => Esub e)) (by
      rw [card_insert_of_not_mem ze,E2,I3])
  have te : t∈C.E := by
    have v : t∈insert z C.E := by rwa [cover]
    exact (mem_insert.mp v).resolve_left zt.ne.symm
  obtain ⟨x,xa⟩ := card_pos.mp C.Apos
  have xh := C.A_sub_H xa
  have xz : x≠z := fun e => C.I_not_A zi (e ▸ xa)
  have xhigh := (S.degree x z xz).resolve_right low
  have xt := C.tight_joins_E xa te xhigh (by omega)
  have no : ¬G.Adj x z := fun e => ze (C.local_a_d2 xa (C.I_sub_H zi) (C.I_not_A zi) e)
  have fb : C.B⊆DistanceTwo G x := by
    intro y yb
    have yz : y≠z := fun e => C.I_not_B zi (e ▸ yb)
    have yh := (S.degree y z yz).resolve_right low
    have ty := C.swap.tight_joins_E yb (eq ▸ te) yh (by change C.B.card+C.F.card=4; have ec := congrArg Finset.card eq; omega)
    exact C.d2_cross_group xa yb (C.no_cross_of_E_sub_I Esub xa yb) xt ty.symm
  exact C.no_extra_local xa U2 B2 C.B_sub_H fb (C.I_sub_H zi) (C.I_not_B zi)
    (C.d2_of_local_nonedge xz no xt zt.symm)

private theorem exclusive_low (A2 : C.A.card=2) (B2 : C.B.card=2)
    (W2 : C.W.card=2) (I3 : C.I.card=3)
    (E2 : C.E.card=2) (F2 : C.F.card=2)
    (Esub : C.E⊆C.I) (Fsub : C.F⊆C.I)
    (allA : ∀ x∈C.A,4≤G.degree x) {u : V} (ue : u∈C.E) (uf : u∉C.F) : ¬4≤G.degree u := by
  have ui := Esub ue
  have h : 0<(C.E∩C.F).card := by
    have count := card_union_add_card_inter C.E C.F
    have su : C.E∪C.F⊆C.I := union_subset Esub Fsub
    have le := card_le_card su
    omega
  obtain ⟨v,vf⟩ := card_pos.mp h
  obtain ⟨ve,vF⟩ := mem_inter.mp vf
  obtain ⟨x,xb,xh⟩ := C.high_of_two (show 2≤C.B.card by omega)
  have xt := C.swap.tight_joins_E xb vF xh (by change C.B.card+C.F.card=4; omega)
  have fb : C.A⊆DistanceTwo G x := by
    intro y ya
    have yv := C.tight_joins_E ya ve (allA y ya) (by omega)
    exact C.swap.d2_cross_group xb ya (fun e => C.no_cross_of_E_sub_I Esub ya xb e.symm) xt yv.symm
  have cover : insert u C.F=C.I := eq_of_subset_of_card_le
    (fun w hw => (mem_insert.mp hw).elim (fun e => e.symm ▸ ui) (fun e => Fsub e)) (by
      rw [card_insert_of_not_mem uf,F2,I3])
  have no : ¬G.Adj x u := fun e => uf (C.swap.local_a_d2 xb (C.I_sub_H ui) (C.I_not_B ui) e)
  have forbid : ∀ t∈C.I, ¬G.Adj u t := by
    intro t ti ut
    have tc : t∈insert u C.F := by rwa [cover]
    have tf := (mem_insert.mp tc).resolve_left ut.ne.symm
    have xt' := C.swap.tight_joins_E xb tf xh (by change C.B.card+C.F.card=4; omega)
    have xu : x≠u := fun e => C.I_not_B ui (e ▸ xb)
    exact C.swap.no_extra_local xb W2 A2 C.A_sub_H fb (C.I_sub_H ui) (C.I_not_A ui)
      (C.d2_of_local_nonedge xu no xt' ut.symm)
  exact C.inner_low_of_no_B_no_inner ui uf forbid A2

theorem contra_22 (large : 7≤C.H.card) (A2 : C.A.card=2) (B2 : C.B.card=2) : False := by
  have u := C.high_port_implies_foreign_ge_two A2
  have w := C.swap.high_port_implies_foreign_ge_two B2
  change 2≤C.W.card at w
  have bound := C.port_K_sum
  have U2 : C.U.card=2 := by omega
  have W2 : C.W.card=2 := by omega
  have cap := C.inner_cap (show 2≤C.A.card by omega)
  have count := C.count_H
  have I3 : C.I.card=3 := by omega
  have aw := C.inner_away_cap (show 2≤C.A.card by omega)
  have bw := C.swap.inner_away_cap (show 2≤C.B.card by omega)
  rw [C.swap_I] at bw
  change (C.I\C.F).card≤3-C.B.card at bw
  have ea := C.e_cap
  have fa := C.swap.e_cap
  change C.F.card≤C.W.card at fa
  obtain ⟨E2,Esub⟩ := C.I_count_off_E I3 (by omega) (by omega)
  have bi : C.swap.I.card=3 := by simpa only [C.swap_I] using I3
  have bw' : (C.swap.I\C.swap.E).card≤1 := by rw [C.swap_I]; change (C.I\C.F).card≤1; omega
  obtain ⟨F2,Fsub'⟩ := C.swap.I_count_off_E bi (by change C.F.card≤2; omega) bw'
  have Fsub : C.F⊆C.I := by simpa only [C.swap_I] using Fsub' 
  by_cases eq : C.E=C.F
  · exact C.missing_of_equal_shells A2 B2 U2 I3 E2 Esub eq
  have exclusive (X Y : Finset V) (sx : X.card=2) (sy : Y.card=2) (ne : X≠Y) :
      ∃ z∈X,z∉Y := by
    by_cases h : ∃ z∈X,z∉Y
    · exact h
    have sub : X⊆Y := fun z ze => Classical.byContradiction (fun nf => h ⟨z,ze,nf⟩)
    exact (ne (eq_of_subset_of_card_le sub (by omega))).elim
  obtain ⟨x,xe,xf⟩ := exclusive _ _ E2 F2 eq
  obtain ⟨y,yf,ye⟩ := exclusive _ _ F2 E2 (Ne.symm eq)
  have xny : x≠y := fun e => xf (e.symm ▸ yf)
  have postponeA (low : ¬4≤G.degree x) : ∀ z∈C.B,4≤G.degree z := by
    intro z zb
    exact (S.degree x z (fun e => C.I_not_B (Esub xe) (e.symm ▸ zb))).resolve_left low
  have postponeB (low : ¬4≤G.degree y) : ∀ z∈C.A,4≤G.degree z := by
    intro z za
    exact (S.degree y z (fun e => C.I_not_A (Fsub yf) (e.symm ▸ za))).resolve_left low
  rcases C.all_high_group with ha|hb
  · have lx := C.exclusive_low A2 B2 W2 I3 E2 F2 Esub Fsub ha xe xf
    have ly := C.swap.exclusive_low B2 A2 U2 bi F2 E2 (by simpa only [C.swap_I] using Fsub) (by simpa only [C.swap_I] using Esub) (postponeA lx) yf ye
    exact (S.degree x y xny).elim lx ly
  · have ly := C.swap.exclusive_low B2 A2 U2 bi F2 E2 (by simpa only [C.swap_I] using Fsub) (by simpa only [C.swap_I] using Esub) hb yf ye
    have lx := C.exclusive_low A2 B2 W2 I3 E2 F2 Esub Fsub (postponeB ly) xe xf
    exact (S.degree x y xny).elim lx ly

#print axioms contra_22
end Graffiti189LongestPath.TwoCut.FourSideCtx
