import PendantBound
namespace Graffiti384b.Adjacent15
open Finset SimpleGraph JointRank
open private Pendant16.allowance from PendantSample
open private Repair.triangles_le_choose from Repair384b
open private FiniteRange.bad FiniteRange.count_bad from FiniteRange384b
open private EarCredit.credited from CreditRanks31
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem rows :
    (∀ r : Fin 27,∀ d : Fin 9,r.val+2≤d.val.choose 2 →
      max (FiniteRange.badCount 26 9 d) ((26-d.val).choose 9+377910)≤Pendant16.allowance r) ∧
    (∀ r : Fin 27,426530≤Pendant16.allowance r) ∧
    (∑ r∈range 27,Pendant16.allowance r)=17965158 ∧
    (∀ r : Fin 27,∀ d : Fin 33,r.val+2≤d.val.choose 2 →
      554129≤Pendant16.allowance r+48620*(d.val-4)) := by
  unfold Pendant16.allowance FiniteRange.badCount; simp only [Nat.choose_eq_fast_choose]; decide

/-- Rank a retained high vertex along with the sampled vertices. Its entire rank allowance
is unused, and its pool neighbors each earn an additional charge. -/
theorem reserve (X A : Finset V) {z : V} (sz : X.card=26) (sep : Disjoint X A)
    (zx : z∉X) (za : z∉A)
    (inj : Set.InjOn (trianglesAt G) ((insert z X : Finset V):Set V))
    (lo : ∀ v∈insert z X,2≤trianglesAt G v) (n : Fintype.card V=33)
    (outside : G.degree z≤nbr G z X+4) :
    (∑ v∈X,((X.powersetCard 9).filter (fun s => v∈FiniteRange.bad G X s)).card)+
      (X.filter (fun v => 0<nbr G v A)).card*377910 + 554129 ≤ 17965158 := by
  classical
  let H := insert z X
  let r := rank H (trianglesAt G)
  let hit := fun v => 0<nbr G v A
  let bill := fun v => ((X.powersetCard 9).filter (fun s => v∈FiniteRange.bad G X s)).card
  have hs : H.card=27 := by dsimp [H]; rw [card_insert_of_not_mem zx,sz]
  have rr (v : V) (vm : v∈H) : r v<27 := by
    have m := mem_image_of_mem (rank H (trianglesAt G)) vm
    rwa [rank_range H _ inj,hs,mem_range] at m
  have dc (v : V) (vm : v∈H) : r v+2≤(G.degree v).choose 2 := by
    rw [Nat.add_comm]; exact (rank_lower H (trianglesAt G) inj 2 lo vm).trans (Repair.triangles_le_choose G v)
  have each (v : V) (vm : v∈X) :
      bill v+(if hit v then 377910 else 0)+(if G.Adj z v then 48620 else 0)≤Pendant16.allowance (r v) := by
    have vh : v∈H := mem_insert_of_mem vm
    let d := min (G.degree v) 8
    have sm : d≤8 := min_le_right ..
    have dg : d≤G.degree v := min_le_left ..
    have bound : r v+2≤d.choose 2 := by
      by_cases h : G.degree v≤8
      · rw [show d=G.degree v from min_eq_left h]; exact dc v vh
      · rw [show d=8 from min_eq_right (by omega),show (8:ℕ).choose 2=28 by decide]
        have := rr v vh; omega
    have tab := rows.1 ⟨r v,rr v vh⟩ ⟨d,by omega⟩ bound
    dsimp only at tab
    have single {w : V} (wo : w∉X) (vw : G.Adj v w) : bill v+377910≤Pendant16.allowance (r v) := by
      have b := EarCredit.credited G vm wo vw 9
      rw [sz] at b
      have mono := Nat.choose_le_choose 9 (show 26-G.degree v≤26-d by omega)
      exact (Nat.add_le_add_right (b.trans mono) _).trans ((le_max_right ..).trans tab)
    by_cases hv : hit v
    · obtain ⟨w,wm⟩ := card_pos.mp hv
      obtain ⟨wa,vw⟩ := mem_filter.mp wm
      have wx : w∉X := fun h => disjoint_left.mp sep h wa
      rw [if_pos hv]
      by_cases zv : G.Adj z v
      · have zero : bill v=0 := card_eq_zero.mpr (eq_empty_of_forall_not_mem (by
          intro s sm
          have lack := (mem_filter.mp (mem_filter.mp sm).2).2
          have good := PinnedColor34.two G (fun p : w=z => za (p ▸ wa)) vw zv.symm
            (mem_union_left s (mem_compl.mpr wx)) (mem_union_left s (mem_compl.mpr zx))
          omega))
        rw [zero,if_pos zv]; exact rows.2.1 ⟨_,rr v vh⟩
      · simpa only [if_neg zv,Nat.add_zero] using single wx vw
    · rw [if_neg hv,Nat.add_zero]
      by_cases zv : G.Adj z v
      · rw [if_pos zv]; have := single zx zv.symm; omega
      · rw [if_neg zv,Nat.add_zero]; have b := FiniteRange.count_bad G X 9 d v vm dg (by omega)
        rw [sz] at b; exact b.trans ((le_max_left ..).trans tab)
  have sum := sum_le_sum (s:=X) each
  have fee : (∑ v∈X,if hit v then 377910 else 0)=(X.filter hit).card*377910 := by rw [←sum_filter]; simp
  have fee2 : (∑ v∈X,if G.Adj z v then 48620 else 0)=nbr G z X*48620 := by rw [←sum_filter]; simp [nbr]
  rw [sum_add_distrib,sum_add_distrib,fee,fee2] at sum
  have total := sum_by_rank H _ inj Pendant16.allowance
  rw [hs,rows.2.2.1] at total
  change (∑ v∈insert z X,Pendant16.allowance (r v))=_ at total
  rw [sum_insert zx] at total
  have zh : z∈H := mem_insert_self ..
  have gd := n ▸ G.degree_lt_card_verts z
  have refund := rows.2.2.2 ⟨r z,rr z zh⟩ ⟨G.degree z,gd⟩ (dc z zh)
  dsimp only at refund
  change (∑ v∈X,bill v)+(X.filter hit).card*377910+554129≤17965158
  omega

/-- The rank reserve pays for the shortfall with only thirteen credited pool vertices. -/
theorem pool (n : Fintype.card V=33) (X O A : Finset V) {z : V} (sz : X.card=26)
    (os : O.card=2) (sep : Disjoint X O) (sa : Disjoint X A)
    (safe : ∀ v∈O,2≤nbr G v (X∪O)ᶜ) (away : ∀ v∈X,∀ w∈O,¬G.Adj v w)
    (zx : z∉X) (za : z∉A)
    (inj : Set.InjOn (trianglesAt G) ((insert z X : Finset V):Set V))
    (lo : ∀ v∈insert z X,2≤trianglesAt G v)
    (outside : G.degree z≤nbr G z X+4)
    (hits : 13≤(X.filter (fun v => 0<nbr G v A)).card) : gamma G≤17 := by
  classical
  let K := X.powersetCard 9
  let B := FiniteRange.bad G X
  have cap := reserve G X A sz sa zx za inj lo n outside
  have trans : (∑ s∈K,(B s).card) = ∑ v∈X,(K.filter (fun s => v∈B s)).card := by
    have inc (s : Finset V) : B s⊆X := (filter_subset ..).trans sdiff_subset
    calc _ = ∑ s∈K,∑ v∈X,if v∈B s then 1 else 0 := by
              simp [sum_boole,filter_mem_eq_inter,inter_eq_right.mpr (inc _)]
         _ = _ := by rw [sum_comm]; simp [sum_boole]
  by_contra! bad
  have each (s : Finset V) (sm : s∈K) : 4≤(B s).card := by
    have tr := Pendant16.trial G X O s sep safe away
    obtain ⟨sub,k⟩ := mem_powersetCard.mp sm
    rw [card_sdiff sub,sz,k,os,n] at tr
    change 4≤(FiniteRange.bad G X s).card; omega
  have mass := sum_le_sum each
  rw [sum_const,smul_eq_mul,trans] at mass
  have size : K.card=3124550 := by dsimp [K]; rw [card_powersetCard,sz,Nat.choose_eq_fast_choose]; decide
  rw [size] at mass
  change (∑ v∈X,(K.filter (fun s => v∈B s)).card)+_+_≤_ at cap
  omega

end Graffiti384b.Adjacent15
#print axioms Graffiti384b.Adjacent15.reserve
#print axioms Graffiti384b.Adjacent15.pool
