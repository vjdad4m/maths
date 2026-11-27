import DegreeFiveReverseMissTwo189
import DegreeFiveReverseOverlap189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph Finset
open private Shore shore_off shore_closed from DegreeFiveActualCut189
open private secondShore from DegreeFiveDistanceTwoThreeClose189
open private Cmp portColor from DegreeFiveThreeForeignImpossible189
open private local_shell_comes_from_port from DegreeFiveNonmixedThreeFour189
open private local_d2_plus_foreign_le_five nonmixed_shell_nonports from DegreeFiveReverseSupport189
open private high_b_cannot_miss_two_shell from DegreeFiveReverseMissTwo189
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

/-- Overlap at the three-point b-shell forces a universal nonport
block and violates the b-porter's local distance-two budget. -/
theorem no_three_b_shell_in_all_high_reverse
    (hc : G.Connected) (two : G.dist a b=2)
    (even : ∀ x,(EvenFrom G x).card ≤ 6)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (none : ∀ w∈Shore D,¬(G.Adj a w ∧ G.Adj b w))
    (nonmix : ∀ u∈portColor D a,∀ v∈portColor D b,¬G.Adj u v)
    (cA : (portColor C a).card=4) (cB : (portColor C b).card=3)
    (pA : (portColor D a).card=2) (pB : (portColor D b).card=3)
    (eA : (secondShore D a).card ≤ 4) (eB : (secondShore D b).card=3)
    (high : ∀ w∈Shore D,5 ≤ G.degree w)
    {e : V} (ee : e∈secondShore D a) (ef : e∈secondShore D b) : False := by
  classical
  let A := portColor D a
  let B := portColor D b
  let E := secondShore D a
  let F := secondShore D b
  have a2 : A.card=2 := pA
  have b3 : B.card=3 := pB
  have e4 : E.card ≤ 4 := eA
  have f3 : F.card=3 := eB
  obtain ⟨u,ua,ue⟩ := local_shell_comes_from_port hc two (.inl rfl) ee
  obtain ⟨q,qb,qe⟩ := local_shell_comes_from_port hc two (.inr rfl) ef
  obtain ⟨ud,au⟩ := mem_filter.mp ua
  obtain ⟨qd,bq⟩ := mem_filter.mp qb
  have unb : ¬G.Adj b u := fun bu=>none u ud ⟨au,bu⟩
  have cutNe {s t : V} (sa : s∈A) (tb : t∈B) : s≠t := by
    intro st
    obtain ⟨_,as⟩ := mem_filter.mp sa
    obtain ⟨td,bt⟩ := mem_filter.mp tb
    exact none t td ⟨st ▸ as,bt⟩
  have q2 : q∈secondShore D u :=
    mem_inter.mpr ⟨qd,d2 hc (cutNe ua qb) (nonmix u ua q qb) ue qe.symm⟩
  have cap : (secondShore D u).card ≤ 1 := by
    have h := local_d2_plus_foreign_le_five hc even cd ua
    rw [cA] at h
    omega
  have uniq {w : V} (hw : w∈secondShore D u) : w=q := by
    by_contra neq
    have h := one_lt_card.mpr ⟨w,hw,q,q2,neq⟩
    omega
  let N := (Shore D).filter (G.Adj u)
  let H := insert u N
  have rEx : ∃ r∈B,r≠q := by
    obtain ⟨v,vb,w,wb,vw⟩ := one_lt_card.mp (show 1<B.card by omega)
    by_cases vq : v=q
    · exact ⟨w,wb,fun wq=>vw (vq.trans wq.symm)⟩
    exact ⟨v,vb,vq⟩
  obtain ⟨r,rb,rq⟩ := rEx
  obtain ⟨rd,br⟩ := mem_filter.mp rb
  have deny {w : V} (uw : G.Adj u w) : ¬G.Adj r w := by
    intro rw
    exact rq (uniq (mem_inter.mpr ⟨rd,d2 hc (cutNe ua rb) (nonmix u ua r rb) uw rw.symm⟩))
  have notF {w : V} (wn : w∈N) (we : w≠e) : w∉F := by
    intro wf
    exact high_b_cannot_miss_two_shell hc pB (by omega) rb (fun ar=>none r rd ⟨ar,br⟩)
      (high r rd) ef wf we.symm (deny ue) (deny (mem_filter.mp wn).2)
  have non {w : V} (we : w∈E) : ¬G.Adj a w ∧ ¬G.Adj b w :=
    nonmixed_shell_nonports hc two none nonmix (.inl ⟨rfl,rfl⟩) we
  have hCover : H⊆A∪E := by
    intro w wh
    rcases mem_insert.mp wh with rfl|wn
    · exact mem_union_left _ ua
    obtain ⟨wd,uw⟩ := mem_filter.mp wn
    by_cases aw : G.Adj a w
    · exact mem_union_left _ (mem_filter.mpr ⟨wd,aw⟩)
    have ne : a≠w := fun h=>(shore_off D).1 (h.symm ▸ wd)
    exact mem_union_right _ (mem_inter.mpr ⟨wd,d2 hc ne aw au uw⟩)
  have nhSub : G.neighborFinset u⊆insert a N := by
    intro w wn
    have uw := (mem_neighborFinset G _ _).mp wn
    rcases shore_closed D u ud w uw with rfl|rfl|wd
    · exact mem_insert_self _ _
    · exact (unb uw.symm).elim
    exact mem_insert_of_mem (mem_filter.mpr ⟨wd,uw⟩)
  have picked : ∃ w∈N,w∈E ∧ w≠e := by
    apply Classical.byContradiction
    intro no
    have sub : N⊆(A.erase u)∪{e} := by
      intro w wn
      rcases mem_union.mp (hCover (mem_insert_of_mem wn)) with wa|we
      · exact mem_union_left _ (mem_erase.mpr ⟨(mem_filter.mp wn).2.ne.symm,wa⟩)
      have wEq : w=e := Classical.byContradiction (fun h=>no ⟨w,wn,we,h⟩)
      exact mem_union_right _ (mem_singleton.mpr wEq)
    have h := (card_le_card nhSub).trans (card_insert_le _ _)
    have k := (card_le_card sub).trans (card_union_le _ _)
    have cnt : (A.erase u).card=1 := by
      rw [card_erase_of_mem (show u∈A from ua),a2]
    rw [card_neighborFinset_eq_degree] at h
    rw [cnt,card_singleton] at k
    have d := high u ud
    omega
  have closed {w : V} (wn : w∈N) (we : w∈E) (neq : w≠e) :
      G.neighborFinset w⊆H.erase w := by
    intro y ym
    have wy := (mem_neighborFinset G _ _).mp ym
    refine mem_erase.mpr ⟨wy.ne.symm,?_⟩
    have wd := (mem_inter.mp we).1
    rcases shore_closed D w wd y wy with rfl|rfl|yd
    · exact ((non we).1 wy.symm).elim
    · exact ((non we).2 wy.symm).elim
    by_cases yh : y∈H
    · exact yh
    have yu : y≠u := fun h=>yh (mem_insert.mpr (.inl h))
    have uy : ¬G.Adj u y := fun h=>yh (mem_insert_of_mem (mem_filter.mpr ⟨yd,h⟩))
    have yq : y=q := uniq (mem_inter.mpr ⟨yd,d2 hc yu.symm uy (mem_filter.mp wn).2 wy⟩)
    have qw : G.Adj q w := yq ▸ wy.symm
    have bw : b≠w := fun eq=>(shore_off D).2 (eq.symm ▸ wd)
    have wf : w∈F := mem_inter.mpr ⟨wd,d2 hc bw (non we).2 bq qw⟩
    exact (notF wn neq wf).elim
  obtain ⟨t,tn,te,te'⟩ := picked
  have h6 : 6≤H.card := by
    have k := card_le_card (closed tn te te')
    have tt : t∈H := mem_insert_of_mem tn
    rw [card_erase_of_mem tt,card_neighborFinset_eq_degree] at k
    have d := high t (mem_inter.mp te).1
    omega
  have u6 : H.card≤6 := (card_le_card hCover).trans ((card_union_le A E).trans (by omega))
  have eq : H=A∪E := eq_of_subset_of_card_le hCover ((card_union_le A E).trans (by omega))
  have enum : E.card=4 := by
    have k := (card_le_card hCover).trans (card_union_le A E)
    omega
  let T := E.erase e
  have t3 : T.card=3 := by rw [card_erase_of_mem (show e∈E from ee),enum]
  have sub : T⊆secondShore D q := by
    intro w wt
    obtain ⟨wne,we⟩ := mem_erase.mp wt
    have wd := (mem_inter.mp we).1
    have uh : w∈H := by rw [eq]; exact mem_union_right _ we
    have wn : w∈N := by
      rcases mem_insert.mp uh with eu|h
      · exact ((non we).1 (eu.symm ▸ au)).elim
      exact h
    have off : w∉F := notF wn wne
    have qn : ¬G.Adj q w := fun qw=>off (mem_inter.mpr ⟨wd,
      d2 hc (fun h=>(shore_off D).2 (h.symm ▸ wd)) (non we).2 bq qw⟩)
    have wh : G.neighborFinset w=H.erase w := by
      apply eq_of_subset_of_card_le (closed wn we wne)
      rw [card_neighborFinset_eq_degree,card_erase_of_mem uh]
      have d := high w wd
      omega
    have eh : e∈H := mem_insert_of_mem (mem_filter.mpr ⟨(mem_inter.mp ee).1,ue⟩)
    have ew : G.Adj e w :=
      ((mem_neighborFinset G _ _).mp (wh.symm ▸ mem_erase.mpr ⟨wne.symm,eh⟩)).symm
    have ne : q≠w := fun h=>(non we).2 (h ▸ bq)
    exact mem_inter.mpr ⟨wd,d2 hc ne qn qe ew⟩
  have cnt := card_le_card sub
  have bound := local_d2_plus_foreign_le_five hc even cd qb
  rw [cB] at bound
  omega

#print axioms no_three_b_shell_in_all_high_reverse
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
