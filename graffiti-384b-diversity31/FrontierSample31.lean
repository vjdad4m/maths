import Diversity33Finish

namespace Graffiti384b.Frontier31
open Finset SimpleGraph CliqueChoice CliqueSample LowSample
open private FiniteRange.bad FiniteRange.count_bad from FiniteRange384b
open private Repair.triangles_le_choose from Repair384b
open private LowSample.delta LowSample.weight from LowSample384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def cutoff (flag : ℕ) := if flag=0 then 8 else 9
private def upper (flag p j : ℕ) := if j=3 ∧ p=0 then 3 else
  if j≤cutoff flag then RankTable.cap j 3+1 else j.choose 2+1
private def limit (flag h p j : ℕ) := min (h-p) (h+(upper flag p j-(if j=flag then 1 else 0))-31-p)
private def quota (flag : ℕ) := if flag=0 then 31 else 30
private def missing (j : ℕ) := if j=3 then 2 else 5
private theorem monotone : ∀ j d : Fin 11, d.val≤j.val → RankTable.cap d 3≤RankTable.cap j 3 := by decide

private theorem table {flag h p : ℕ} (fs : flag=0 ∨ flag=3 ∨ flag=4) (hs : h=29 ∨ h=30) (ps : p=0 ∨ p=1) :
    let m := h-p
    12≤m ∧ envelope m 11 ∧ reward m 11 ∧
      6*(15*m.choose 11+UnifiedSample.chargeAt m 11 (limit flag h p)) <
        6*(m-11)*m.choose 11+(quota flag-h)*(6*(m-2).choose 9)+6*p*bonus m 11 3 := by
  rcases fs with rfl|rfl|rfl <;> rcases hs with rfl|rfl <;> rcases ps with rfl|rfl <;>
    unfold quota limit upper cutoff RankTable.cap envelope reward UnifiedSample.chargeAt LowSample.delta LowSample.weight bonus FiniteRange.badCount <;>
    simp only [FiniteRange.badCount,Nat.choose_eq_fast_choose] <;> decide

/-- One missing low-degree score or an additional nonleaf suffices. -/
theorem sampled {flag : ℕ} (fs : flag=0 ∨ flag=3 ∨ flag=4)
    (t : (types G).card=31) (q : quota flag≤(nonleaves G).card) (localCap : ∀ v,G.degree v≤cutoff flag → trianglesAt G v≤RankTable.cap (G.degree v) 3)
    (absent : flag≠0 → ∀ v,G.degree v=flag → trianglesAt G v≠missing flag) :
    gamma G≤bound G := by
  classical
  by_contra! fail
  let h := (high G).card
  have lim := type_bound G
  have miss : ((high G).card+1)/2 < ((types G).card+1)/2 :=
    Nat.lt_of_not_ge (fun le => (not_lt_of_ge (exact_of_high G le)) fail)
  have hs : h=29 ∨ h=30 := by dsimp [h]; omega
  letI : Nonempty V := by obtain ⟨v,_⟩ := card_pos.mp (show 0<(high G).card by change 0<h; omega); exact ⟨v⟩
  obtain ⟨P,ch⟩ := choose_from G ({3} : Finset ℕ) (by simp)
  let f := P.image (G.degree ·)
  have only : f⊆{3} := ch.levels
  have ps : P.card=0 ∨ P.card=1 := by
    have size := card_le_card only
    change (P.image (G.degree ·)).card≤1 at size
    rw [card_image_of_injOn ch.unique] at size; omega
  let m := h-P.card
  let s := high G\P
  have sz : s.card=m := card_sdiff ch.high_sub
  obtain ⟨room,env,rew,strict⟩ := table fs hs ps
  change 12≤m at room
  have deg (z : V) (hz : z∈P) : G.degree z=3 := mem_singleton.mp (only (mem_image_of_mem _ hz))
  have dist (j : ℕ) (jj : j∈range 11) (pos : 3≤j) : (s.filter (fun z => G.degree z≤j)).card≤limit flag h P.card j := by
    let H := (high G).filter (fun z => G.degree z≤j)
    have jt := mem_range.mp jj
    have cap (v : V) (vd : G.degree v≤j) : trianglesAt G v<upper flag P.card j := by
      by_cases under : j≤cutoff flag
      · have up := localCap v (vd.trans under)
        have mono := monotone ⟨j,jt⟩ ⟨G.degree v,by omega⟩ vd
        change RankTable.cap (G.degree v) 3≤RankTable.cap j 3 at mono
        unfold upper; rw [if_pos under]
        split_ifs with special
        · obtain ⟨rfl,empty⟩ := special
          by_cases three : G.degree v=3
          · rw [three] at up
            change trianglesAt G v≤3 at up
            by_contra! big
            have inF := ch.covers v (mem_singleton.mpr three) (by rw [three]; change trianglesAt G v=3; omega)
            rw [card_eq_zero.mp empty] at inF; simp at inF
          · have small := monotone ⟨2,by decide⟩ ⟨G.degree v,by omega⟩ (by change G.degree v≤2; omega)
            change RankTable.cap (G.degree v) 3≤1 at small; omega
        · omega
      · have eight : 8≤cutoff flag := by unfold cutoff; split_ifs <;> decide
        have le := (Repair.triangles_le_choose G v).trans (Nat.choose_le_choose 2 vd)
        simp [upper,show j≠3 by omega,under]; omega
    let scores := if j=flag then (range (upper flag P.card j)).erase (missing flag) else range (upper flag P.card j)
    have allowed (v : V) (vd : G.degree v≤j) : trianglesAt G v∈scores := by
      have mem := mem_range.mpr (cap v vd)
      by_cases ej : j=flag
      · unfold scores; rw [if_pos ej]; apply mem_erase.mpr ⟨?_,mem⟩
        by_cases same : G.degree v=flag
        · exact absent (by omega) _ same
        · have eight : 8≤cutoff flag := by unfold cutoff; split_ifs <;> decide
          have u := localCap v (by omega)
          rcases fs with f|f|f
          · omega
          · have h2 := monotone ⟨2,by decide⟩ ⟨G.degree v,by omega⟩ (by change G.degree v≤2; omega)
            change RankTable.cap (G.degree v) 3≤1 at h2
            rw [f]; change trianglesAt G v≠2; omega
          · have h3 := monotone ⟨3,by decide⟩ ⟨G.degree v,by omega⟩ (by change G.degree v≤3; omega)
            change RankTable.cap (G.degree v) 3≤3 at h3
            rw [f]; change trianglesAt G v≠5; omega
      · simpa [scores,ej] using mem
    have sizeS : scores.card=upper flag P.card j-(if j=flag then 1 else 0) := by
      by_cases eq : j=flag
      · have mem : missing flag∈range (upper flag P.card j) := by
          rw [mem_range]; rcases fs with f|f|f
          · omega
          · rw [eq,f]; rcases ps with h|h <;> rw [h] <;> decide
          · rw [eq,f]; rcases ps with h|h <;> rw [h] <;> decide
        simp only [scores,if_pos eq,card_erase_of_mem mem,card_range]
      · simp [scores,eq]
    have coverage : types G ⊆ ((high G)\H).image (trianglesAt G) ∪ scores := by
      intro a ha
      obtain ⟨z,_,rfl⟩ := mem_image.mp ha
      by_cases small : G.degree z≤j
      · exact mem_union_right _ (allowed z small)
      · exact mem_union_left _ (mem_image.mpr ⟨z,mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_univ _,by omega⟩,
          fun hz => small (mem_filter.mp hz).2⟩,rfl⟩)
    have card := (card_le_card coverage).trans (card_union_le _ _)
    rw [t,sizeS] at card
    have im := card_image_le (s:=high G\H) (f:=trianglesAt G)
    have num : (high G\H).card+H.card=h := card_sdiff_add_card_eq_card (filter_subset _ _)
    have sub : P⊆H := fun z hz => mem_filter.mpr ⟨ch.high_sub hz,(deg z hz) ▸ pos⟩
    have eq : s.filter (fun z => G.degree z≤j)=H\P := by ext z; simp [s,H,and_assoc,and_comm,and_left_comm]
    have count := card_sdiff_add_card_eq_card sub
    exact le_min ((card_filter_le _ _).trans_eq sz) (by rw [eq]; omega)
  have obs := UnifiedSample.extraObstruction G ch 11 (limit flag h P.card) dist (fun _ => 0)
    (by intro z hz; rw [Nat.add_zero]; exact FiniteRange.count_bad G _ 11 _ z hz (min_le_left _ _) (by change _<s.card; omega))
    (by decide) (sz ▸ env) (sz ▸ rew) fail
  dsimp only at obs
  have cardf : f.card=P.card := card_image_of_injOn ch.unique
  have sum : (∑ d∈f,bonus m 11 d)=P.card*bonus m 11 3 := by
    calc
      _ = ∑ _d∈f,bonus m 11 3 := sum_congr rfl (fun d dm => by rw [mem_singleton.mp (only dm)])
      _ = _ := by simp [cardf]
  have sub : high G⊆nonleaves G := fun z hz => mem_filter.mpr ⟨mem_univ _,by have := (mem_filter.mp hz).2; omega⟩
  have total : (twos G).card+h=(nonleaves G).card := card_sdiff_add_card_eq_card sub
  simp only [sum_const_zero,Nat.mul_zero,Nat.add_zero,t] at obs
  change 6*(h-f.card-11)*(h-f.card).choose 11+(twos G).card*(6*(h-f.card-2).choose 9)+6*(∑ d∈f,bonus (h-f.card) 11 d) ≤
    6*(15*(h-f.card).choose 11+UnifiedSample.chargeAt (h-f.card) 11 (limit flag h P.card)) at obs
  rw [cardf] at obs
  change 6*(m-11)*m.choose 11+(twos G).card*(6*(m-2).choose 9)+6*(∑ d∈f,bonus m 11 d)≤
    6*(15*m.choose 11+UnifiedSample.chargeAt m 11 (limit flag h P.card)) at obs
  have extra := Nat.mul_le_mul_right (6*(m-2).choose 9) (show quota flag-h≤(twos G).card by omega)
  rw [sum,←Nat.mul_assoc 6 P.card] at obs
  change 6*(15*m.choose 11+UnifiedSample.chargeAt m 11 (limit flag h P.card)) <
    6*(m-11)*m.choose 11+(quota flag-h)*(6*(m-2).choose 9)+6*P.card*bonus m 11 3 at strict
  omega

end Graffiti384b.Frontier31
#print axioms Graffiti384b.Frontier31.sampled
