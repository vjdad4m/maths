import CliquePool
namespace Graffiti384b.AdjacentFull
open Finset SimpleGraph JointRank Adjacent12
open private Adjacent12.row Adjacent12.bonus Adjacent12.refund Adjacent12.active_fiber from CliquePool
open private Repair.triangles_le_choose from Repair384b
open private FiniteRange.bad FiniteRange.count_bad from FiniteRange384b
open private EarCredit.credited from CreditRanks31
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

private def cost (r : ℕ) := if r<26 then Adjacent12.row r else 284310
private def reserve (k : ℕ) := cost (min 28 ((k+1).choose 2-1))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 5000000 in
private theorem numeric :
    (∀ r : Fin 29,∀ d : Fin 11,3≤d.val → (r.val+2≤d.val.choose 2 ∨ d.val=10) →
      max (FiniteRange.badCount 26 9 d) ((26-d.val).choose 9+260000)≤cost r+Adjacent12.refund r d) ∧
    (∑ r∈range 29,cost r)=15942483 ∧
    (∀ r : Fin 29,∀ k : Fin 10,r.val+2≤1+(k.val+1).choose 2 → reserve k≤cost r) ∧
    (∀ x y m : Fin 10,x.val+y.val≤m.val →
      15942483+3707≤12498200+260000*m.val+reserve x+reserve y+reserve m) := by
  unfold cost reserve Adjacent12.row Adjacent12.refund Adjacent12.bonus FiniteRange.badCount
  simp only [Nat.choose_eq_fast_choose]; decide

private theorem lower (n : Fintype.card V=33) (X O : Finset V) (sz : X.card=26)
    (os : O.card=2) (sep : Disjoint X O)
    (safe : ∀ v∈O,2≤nbr G v (X∪O)ᶜ) (away : ∀ v∈X,∀ w∈O,¬G.Adj v w)
    (inj : Set.InjOn (trianglesAt G) (X:Set V)) (bad : 17<gamma G) :
    3124550*4+(∑ v∈X,((X.powersetCard 9).filter (fun s => v∈activated G X s)).card)≤
      ∑ v∈X,((X.powersetCard 9).filter (fun s => v∈FiniteRange.bad G X s)).card := by
  classical
  let K := X.powersetCard 9
  let B := FiniteRange.bad G X
  let P := activated G X
  have swap (F : Finset V→Finset V) (inc : ∀ s∈K,F s⊆X) :
      (∑ s∈K,(F s).card)=∑ v∈X,(K.filter (fun s => v∈F s)).card := by
    calc _ = ∑ s∈K,∑ v∈X,if v∈F s then 1 else 0 := by
              apply sum_congr rfl
              intro s sm; simp [sum_boole,filter_mem_eq_inter,inter_eq_right.mpr (inc s sm)]
         _ = _ := by rw [sum_comm]; simp [sum_boole]
  have each (s : Finset V) (sm : s∈K) : 4+(P s).card≤(B s).card := by
    obtain ⟨sub,k⟩ := mem_powersetCard.mp sm
    have tr := Adjacent12.trial G X O s sep safe away sub inj
    rw [card_sdiff sub,sz,k,os,n] at tr
    change 4+(activated G X s).card≤(FiniteRange.bad G X s).card; omega
  have mass := sum_le_sum each
  rw [sum_add_distrib,sum_const,smul_eq_mul,swap B (fun _ _ => (filter_subset ..).trans sdiff_subset),
    swap P (fun _ sm => (filter_subset ..).trans (mem_powersetCard.mp sm).1)] at mass
  have size : K.card=3124550 := by dsimp [K]; rw [card_powersetCard,sz,Nat.choose_eq_fast_choose]; decide
  rw [size] at mass
  exact mass



/-- Three distinct retained high vertices have rank allowances which none
of the twenty-six sampled vertices can spend. The same contacts that supply
retained neighbors also bound all three retained vertices' triangle counts. -/
theorem exact_pool (n : Fintype.card V=33) (X O : Finset V) {a b z : V}
    (ab : a≠b) (az : a≠z) (bz : b≠z)
    (sz : X.card=26) (os : O.card=2) (sep : Disjoint X O)
    (safe : ∀ v∈O,2≤nbr G v (X∪O)ᶜ) (away : ∀ v∈X,∀ w∈O,¬G.Adj v w)
    (xh : X⊆high G) (xj : Disjoint X ({a,b,z}:Finset V))
    (inj : Set.InjOn (trianglesAt G) ((insert a (insert b (insert z X)):Finset V):Set V))
    (lo : ∀ v∈insert a (insert b (insert z X)),2≤trianglesAt G v)
    (x y m : ℕ) (xy : x+y≤m) (contacts : (X.filter (fun i => 0<nbr G i {a,b,z})).card=m)
    (sa : trianglesAt G a≤1+(x+1).choose 2) (sb : trianglesAt G b≤1+(y+1).choose 2)
    (sc : trianglesAt G z≤1+(m+1).choose 2) : gamma G≤17 := by
  classical
  let H := insert a (insert b (insert z X))
  let J : Finset V := {a,b,z}
  have ax : a∉X := fun h => disjoint_left.mp xj h (mem_insert_self ..)
  have bx : b∉X := fun h => disjoint_left.mp xj h (by simp)
  have zx : z∉X := fun h => disjoint_left.mp xj h (by simp)
  have ai : a∉insert b (insert z X) := by simp [ab,az,ax]
  have bi : b∉insert z X := by simp [bz,bx]
  have hs : H.card=29 := by dsimp [H]; rw [card_insert_of_not_mem ai,card_insert_of_not_mem bi,card_insert_of_not_mem zx,sz]
  have xin : X⊆H := (subset_insert ..).trans ((subset_insert ..).trans (subset_insert ..))
  have xi := inj.mono (show (X:Set V)⊆H from xin)
  by_contra! bad
  have small : m<10 := by
    by_contra! many
    exact (not_lt_of_ge (Adjacent12.pool G n X O J sz os sep xj safe away xh xi (fun i im => lo i (xin im)) (contacts ▸ many))) bad
  let r := rank H (trianglesAt G)
  have limit (v : V) (vh : v∈H) : r v<29 := by
    have rk := mem_image_of_mem (rank H (trianglesAt G)) vh
    rwa [rank_range H _ inj,hs,mem_range] at rk
  have paid (v : V) (vh : v∈H) (k : ℕ) (ks : k<10) (score : trianglesAt G v≤1+(k+1).choose 2) :
      reserve k≤cost (r v) := by
    apply numeric.2.2.1 ⟨r v,limit v vh⟩ ⟨k,ks⟩
    have lr := rank_lower H (trianglesAt G) inj 2 lo vh
    change r v+2≤1+(k+1).choose 2
    change 2+r v≤trianglesAt G v at lr
    omega
  have pa := paid a (mem_insert_self ..) x (by omega) sa
  have pb := paid b (mem_insert_of_mem (mem_insert_self ..)) y (by omega) sb
  have pz := paid z (mem_insert_of_mem (mem_insert_of_mem (mem_insert_self ..))) m small sc
  have final := numeric.2.2.2 ⟨x,by omega⟩ ⟨y,by omega⟩ ⟨m,small⟩ xy
  dsimp only at final

  let hit := fun v => 0<nbr G v J
  let bill := fun v => ((X.powersetCard 9).filter (fun s => v∈FiniteRange.bad G X s)).card
  let act := fun v => ((X.powersetCard 9).filter (fun s => v∈activated G X s)).card
  have each (v : V) (vm : v∈X) : bill v+(if hit v then 260000 else 0)≤cost (r v)+act v := by
    have vh := xin vm
    have rk := limit v vh
    have lr := rank_lower H (trianglesAt G) inj 2 lo vh
    let d := min (G.degree v) 10
    have sm : d≤10 := min_le_right ..
    have dg : d≤G.degree v := min_le_left ..
    have dc : r v+2≤d.choose 2 ∨ d=10 := by
      by_cases h : G.degree v≤10
      · rw [show d=G.degree v from min_eq_left h,Nat.add_comm]; exact Or.inl (lr.trans (Repair.triangles_le_choose G v))
      · exact Or.inr (min_eq_right (by omega))
    have tab := numeric.1 ⟨r v,rk⟩ ⟨d,by omega⟩ (le_min (mem_filter.mp (xh vm)).2 (by decide)) dc
    dsimp only at tab
    have rc : Adjacent12.refund (r v) d≤act v := by
      unfold Adjacent12.refund; split_ifs with eq
      · have lt : d<10 := by
          by_cases ten : d=10
          · rw [ten,show (10:ℕ).choose 2=45 by decide] at eq; omega
          · omega
        have de : d=G.degree v := by dsimp [d] at *; omega
        have sat : saturated G v := by
          unfold saturated; apply Nat.le_antisymm (Repair.triangles_le_choose G v)
          rw [←de,←eq,Nat.add_comm]; exact lr
        exact Adjacent12.active_fiber G X sz vm sat 8 d dg (by omega)
      · exact Nat.zero_le _
    apply le_trans _ (Nat.add_le_add_left rc _)
    apply le_trans _ tab
    by_cases hv : hit v
    · obtain ⟨w,wm⟩ := card_pos.mp hv
      obtain ⟨wa,vw⟩ := mem_filter.mp wm
      have b := EarCredit.credited G vm (fun wx => disjoint_left.mp xj wx wa) vw 9
      rw [sz] at b
      have mono := Nat.choose_le_choose 9 (show 26-G.degree v≤26-d by omega)
      rw [if_pos hv]; exact (Nat.add_le_add_right (b.trans mono) _).trans (le_max_right ..)
    · have b := FiniteRange.count_bad G X 9 d v vm dg (by omega)
      rw [sz] at b; rw [if_neg hv,Nat.add_zero]; exact b.trans (le_max_left ..)

  have sum := sum_le_sum (s:=X) each
  have fee : (∑ v∈X,if hit v then 260000 else 0)=m*260000 := by rw [←sum_filter]; simp [hit,J,contacts]
  simp only [sum_add_distrib,fee] at sum
  have total := sum_by_rank H _ inj cost
  rw [hs,numeric.2.1] at total
  change (∑ v∈insert a (insert b (insert z X)),cost (r v))=_ at total
  rw [sum_insert ai,sum_insert bi,sum_insert zx] at total
  have mass := lower G n X O sz os sep safe away xi bad
  change 3124550*4+(∑ v∈X,act v)≤∑ v∈X,bill v at mass
  omega

end Graffiti384b.AdjacentFull
#print axioms Graffiti384b.AdjacentFull.exact_pool
