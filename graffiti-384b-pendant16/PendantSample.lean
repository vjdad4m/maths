import RankRepair29
namespace Graffiti384b.Pendant16
open Finset SimpleGraph JointRank
open private Repair.omit_set Repair.triangles_le_choose from Repair384b
open private FiniteRange.bad FiniteRange.count_bad from FiniteRange384b
open private EarCredit.credited from CreditRanks31
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Two fixed omissions whose supporting neighbors all remain outside the pool. -/
theorem trial (X O s : Finset V) (sep : Disjoint X O)
    (safe : ∀ v∈O,2≤nbr G v (X∪O)ᶜ)
    (away : ∀ v∈X,∀ w∈O,¬G.Adj v w) :
    gamma G + (X\s).card + O.card ≤ Fintype.card V + (FiniteRange.bad G X s).card := by
  classical
  let B := FiniteRange.bad G X s
  let H := (X\s)\B
  let T := H∪O
  have hx : H⊆X := sdiff_subset.trans sdiff_subset
  have ot : T⊆X∪O := union_subset_union hx Subset.rfl
  have ok (v : V) (vm : v∈T) : 2≤nbr G v Tᶜ := by
    rcases mem_union.mp vm with vh|vo
    · obtain ⟨xs,nb⟩ := mem_sdiff.mp vh
      have good : 2≤nbr G v (Xᶜ∪s) := Nat.le_of_not_gt (fun h => nb (mem_filter.mpr ⟨xs,h⟩))
      apply good.trans (card_le_card ?_)
      intro w wm
      obtain ⟨wk,vw⟩ := mem_filter.mp wm
      refine mem_filter.mpr ⟨mem_compl.mpr ?_,vw⟩
      intro wt
      rcases mem_union.mp wt with wh|wo
      · exact (mem_union.mp wk).elim (fun z => mem_compl.mp z (hx wh))
          ((mem_sdiff.mp (mem_sdiff.mp wh).1).2)
      · exact away v (hx vh) w wo vw
    · exact (safe v vo).trans (card_le_card (filter_subset_filter _ (compl_subset_compl.mpr ot)))
  have bound := Repair.omit_set G T ok
  have size : T.card=H.card+O.card := card_union_of_disjoint (sep.mono hx Subset.rfl)
  have fit : T.card≤Fintype.card V := card_le_univ _
  have bs : B⊆X\s := filter_subset ..
  have hs := card_sdiff_add_card_eq_card bs
  change H.card+B.card=(X\s).card at hs
  change gamma G + (X\s).card + O.card ≤ Fintype.card V + B.card
  omega

private def allowance (r : ℕ) := if r<2 then 1456730 else if r<5 then 1107890
  else if r<9 then 797810 else if r<14 then 545870 else if r<20 then 470288 else 426530

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem table :
    (∀ r : Fin 26,∀ d : Fin 9,r.val+2≤d.val.choose 2 →
      max (FiniteRange.badCount 26 9 d) ((26-d.val).choose 9+377910)≤allowance r) ∧
    (∑ r∈range 26,allowance r)=17538628 := by
  unfold allowance FiniteRange.badCount; simp only [Nat.choose_eq_fast_choose]; decide

/-- Sum the per-rank deficiency cost for nine draws, charging for every exterior credit. -/
theorem ranked (X A : Finset V) (sz : X.card=26) (sep : Disjoint X A)
    (inj : Set.InjOn (trianglesAt G) (X:Set V)) (lo : ∀ v∈X,2≤trianglesAt G v) :
    (∑ v∈X,((X.powersetCard 9).filter (fun s => v∈FiniteRange.bad G X s)).card) +
      (X.filter (fun v => 0<nbr G v A)).card*377910 ≤ 17538628 := by
  classical
  let r := rank X (trianglesAt G)
  let hit := fun v => 0<nbr G v A
  let bill := fun v => ((X.powersetCard 9).filter (fun s => v∈FiniteRange.bad G X s)).card
  have each (v : V) (vm : v∈X) : bill v + (if hit v then 377910 else 0) ≤ allowance (r v) := by
    have rk := mem_image_of_mem (rank X (trianglesAt G)) vm
    rw [rank_range X _ inj,sz,mem_range] at rk
    have lr := rank_lower X (trianglesAt G) inj 2 lo vm
    let d := min (G.degree v) 8
    have sm : d≤8 := min_le_right .. 
    have dg : d≤G.degree v := min_le_left ..
    have dc : r v+2≤d.choose 2 := by
      by_cases h : G.degree v≤8
      · rw [show d=G.degree v from min_eq_left h,Nat.add_comm]; exact lr.trans (Repair.triangles_le_choose G v)
      · rw [show d=8 from min_eq_right (by omega),show (8:ℕ).choose 2=28 by decide]
        change r v<26 at rk; omega
    have tab := table.1 ⟨r v,rk⟩ ⟨d,by omega⟩ dc
    dsimp only at tab
    by_cases hv : hit v
    · obtain ⟨w,wm⟩ := card_pos.mp hv
      obtain ⟨wa,vw⟩ := mem_filter.mp wm
      have b := EarCredit.credited G vm (fun wx => disjoint_left.mp sep wx wa) vw 9
      rw [sz] at b
      have mono := Nat.choose_le_choose 9 (show 26-G.degree v≤26-d by omega)
      rw [if_pos hv]
      exact (Nat.add_le_add_right (b.trans mono) _).trans ((le_max_right ..).trans tab)
    · have b := FiniteRange.count_bad G X 9 d v vm dg (by omega)
      rw [sz] at b
      rw [if_neg hv,Nat.add_zero]; exact b.trans ((le_max_left ..).trans tab)
  have sum := sum_le_sum (s:=X) each
  have fee : (∑ v∈X,if hit v then 377910 else 0)=(X.filter hit).card*377910 := by
    rw [←sum_filter]; simp
  rw [sum_add_distrib,fee] at sum
  change _ ≤ ∑ v∈X,allowance (rank X (trianglesAt G) v) at sum
  rwa [sum_by_rank X _ inj allowance,sz,table.2] at sum

end Graffiti384b.Pendant16
#print axioms Graffiti384b.Pendant16.trial
#print axioms Graffiti384b.Pendant16.ranked
