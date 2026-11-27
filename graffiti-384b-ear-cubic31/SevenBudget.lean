import SevenFibers
namespace Graffiti384b.Seven
open Finset SimpleGraph JointRank
def fee : ℕ := 980628
def spineFloor : ℕ := 9229968
def tipFloor : ℕ := 10210596
def mark (i : ℕ) := if i<2 then i+3 else i+4
def budget (i : ℕ) := if i=0 then 45349200 else if i=1 then 34210800 else if i≤4 then 24310000
  else if i≤8 then 16302000 else if i≤12 then 10418628 else if i≤17 then 6772128
  else if i≤23 then 4326828 else 3922512

set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
theorem arithmetic :
    (∀ k : Fin 27,∀ b : Fin 23,∀ i j : Fin 3,
      (b.val+i.val+j.val≤10 → mark k≤RankTable.cap (b.val+i.val+j.val) 3) →
      100*weight b j i+fee*(i.val+j.val)≤budget k) ∧
    (∀ k : Fin 27,∀ b : Fin 24,(b.val+3≤10 → mark k≤5+RankTable.cap (b.val+3) 3) →
      spineFloor≤budget k+fee*b.val) ∧
    (∀ k : Fin 27,∀ b : Fin 24,(b.val+2≤10 → mark k≤2+RankTable.cap (b.val+2) 3) →
      tipFloor≤budget k+fee*b.val) ∧
    (∑ i∈range 27,budget i)=330961656 ∧
    330961656<2*spineFloor+2*tipFloor+600*(23:ℕ).choose 8 := by
  unfold mark weight bill FiniteRange.badCount fee spineFloor tipFloor budget RankTable.cap
  simp only [Nat.choose_eq_fast_choose]
  decide

variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
open private ThreeChoice.balance from ThreeBudget33

theorem mass {S T W : Finset V} (st : Disjoint S T) (aw : Disjoint (S∪T) W)
    (ss : S.card=2) (ts : T.card=2) (ws : W.card=23) (fi : Function.Injective (trianglesAt H))
    (vals : ∀ v∈(S∪T)∪W,3≤trianglesAt H v ∧ trianglesAt H v≠5)
    (wc : ∀ v∈W,nbr H v W+nbr H v S+nbr H v T≤10 →
      trianglesAt H v≤RankTable.cap (nbr H v W+nbr H v S+nbr H v T) 3)
    (sc : ∀ v∈S,nbr H v W+3≤10 → trianglesAt H v≤5+RankTable.cap (nbr H v W+3) 3)
    (tc : ∀ v∈T,nbr H v W+2≤10 → trianglesAt H v≤2+RankTable.cap (nbr H v W+2) 3) :
    (∑ w∈W,weight (nbr H w W) (nbr H w T) (nbr H w S))<6*(23:ℕ).choose 8 := by
  classical
  let A := (S∪T)∪W
  let g (v : V) := if trianglesAt H v<5 then trianglesAt H v-2 else trianglesAt H v-3
  have inj : Set.InjOn g (A:Set V) := by
    intro u um v vm eq; have := vals u um; have := vals v vm; apply fi; unfold g at eq; split_ifs at eq <;> omega
  have pos (v : V) (vm : v∈A) : 1≤g v := by have := vals v vm; unfold g; split_ifs <;> omega
  have size : A.card=27 := by dsimp [A]; rw [card_union_of_disjoint aw,card_union_of_disjoint st,ss,ts,ws]
  let r := rank A g
  have valid {v : V} (vm : v∈A) : r v<27 := by
    have m := mem_image_of_mem (rank A g) vm
    rw [rank_range A g inj,size,mem_range] at m; exact m
  have lower {v : V} (vm : v∈A) : mark (r v)≤trianglesAt H v := by
    have b := rank_lower A g inj 1 pos vm
    change 1+r v≤(if trianglesAt H v<5 then trianglesAt H v-2 else trianglesAt H v-3) at b
    have := vals v vm; unfold mark; split_ifs at * <;> omega
  let f (v : V) := budget (r v)
  have bound (v : V) (D : Finset V) : nbr H v D≤D.card := card_filter_le .. 
  have wb (v : V) (vm : v∈W) :
      100*weight (nbr H v W) (nbr H v T) (nbr H v S)+fee*nbr H v S+fee*nbr H v T≤f v := by
    have inc := mem_union_right (S∪T) vm
    have sub : W.filter (H.Adj v)⊆W.erase v := fun x m => mem_erase.mpr ⟨(mem_filter.mp m).2.ne.symm,(mem_filter.mp m).1⟩
    have n := card_le_card sub; rw [card_erase_of_mem vm,ws] at n
    change nbr H v W≤_ at n
    have b := bound v S; have c := bound v T
    have h := arithmetic.1 ⟨_,valid inc⟩ ⟨nbr H v W,by omega⟩ ⟨nbr H v S,by omega⟩ ⟨nbr H v T,by omega⟩
      (fun small => (lower inc).trans (wc v vm small))
    simpa only [Nat.mul_add,Nat.add_assoc] using h
  have sb (v : V) (vm : v∈S) : spineFloor≤f v+fee*nbr H v W := by
    have inc := mem_union_left W (mem_union_left T vm); have := bound v W
    exact arithmetic.2.1 ⟨_,valid inc⟩ ⟨nbr H v W,by omega⟩ (fun small => (lower inc).trans (sc v vm small))
  have tb (v : V) (vm : v∈T) : tipFloor≤f v+fee*nbr H v W := by
    have inc := mem_union_left W (mem_union_right S vm); have := bound v W
    exact arithmetic.2.2.1 ⟨_,valid inc⟩ ⟨nbr H v W,by omega⟩ (fun small => (lower inc).trans (tc v vm small))
  have wsum := sum_le_sum wb; have ssum := sum_le_sum sb; have tsum := sum_le_sum tb
  simp only [sum_add_distrib,←mul_sum] at wsum ssum tsum
  rw [sum_const,nsmul_eq_mul,ss] at ssum; rw [sum_const,nsmul_eq_mul,ts] at tsum
  rw [ThreeChoice.balance H S W,ThreeChoice.balance H T W] at wsum
  have total : (∑ v∈S,f v)+(∑ v∈T,f v)+(∑ v∈W,f v)=330961656 := by
    rw [←sum_union st,←sum_union aw]
    change (∑ v∈A,budget (rank A g v))=_
    rw [sum_by_rank A g inj budget,size]; exact arithmetic.2.2.2.1
  have lim := arithmetic.2.2.2.2
  omega

end Graffiti384b.Seven
#print axioms Graffiti384b.Seven.arithmetic
#print axioms Graffiti384b.Seven.mass
