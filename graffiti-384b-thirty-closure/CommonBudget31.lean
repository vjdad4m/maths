import ThirtyFinish31

namespace Graffiti384b.OneCommon
open Finset SimpleGraph JointRank

def mark (i : ℕ) := if i=0 then 1 else i+3
def row (i : ℕ) := if i=0 then 1279080 else if i≤2 then 684216 else if i≤5 then 486200
  else if i≤9 then 326040 else if i≤13 then 205920 else if i≤18 then 121836 else 66924

def weight (b f i j : ℕ) := i*Seven.weight b j (f+(i-1)) + (2-i)*Seven.weight b j (f+i)

set_option maxHeartbeats 24000000 in
set_option maxRecDepth 65536 in
/-- Finite rank bounds for both kinds of vertices. Each of the two
private neighbors of the score-two cubic has one allowance of 153340. -/
theorem table :
    (∀ r : Fin 25,∀ b : Fin 23,∀ f : Fin 2,∀ i j : Fin 3,
      mark r≤(b.val+(f.val+i.val+j.val)).choose 2 →
      (f.val+i.val+j.val≤2 → b.val+(f.val+i.val+j.val)≤10 →
        mark r≤RankTable.cap (b.val+(f.val+i.val+j.val)) 3) →
      weight b f i j≤row r) ∧
    (∀ r : Fin 25,∀ b : Fin 24,mark r≤(b.val+3).choose 2 →
      2*(23-b.val).choose 8≤row r+153340) ∧
    (∑ r∈range 25,row r)+2*153340=7551356 ∧ 7551356<16*(23:ℕ).choose 8 := by
  unfold mark row weight Seven.weight Seven.bill FiniteRange.badCount RankTable.cap
  simp only [Nat.choose_eq_fast_choose]
  decide

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Average the two independent choices of a retained private neighbor.
The shared vertex contributes a fixed credit wherever it is adjacent. -/
theorem four_fibers {U L W : Finset V} (us : U.card=2) (ls : L.card=2) (ws : W.card=23)
    {w : V} (wm : w∈W) (f : V→ℕ) :
    (∑ x∈U,∑ y∈L,((W.powersetCard 8).filter (fun k => w∈Seven.failures G W k
      (fun v => f v+nbr G v (U.erase x)+nbr G v (L.erase y)))).card) ≤
      weight (nbr G w W) (f w) (nbr G w U) (nbr G w L) := by
  classical
  let B := U.filter (G.Adj w)
  have sub : B⊆U := filter_subset ..
  have sb : B.card=nbr G w U := rfl
  have er (x : V) : (U.erase x).filter (G.Adj w)=B.erase x := by ext y; simp [B,and_assoc,and_left_comm]
  let h (x : V) := Seven.weight (nbr G w W) (nbr G w L) (f w+nbr G w (U.erase x))
  have upper := sum_le_sum (s:=U) (fun x _ => Seven.two_fibers G ls ws wm (fun v => f v+nbr G v (U.erase x)))
  apply upper.trans
  change (∑ x∈U,h x)≤_
  have eq := sum_sdiff sub (f:=h)
  have valA : (∑ x∈U\B,h x)=(U\B).card*Seven.weight (nbr G w W) (nbr G w L) (f w+nbr G w U) := by
    calc _ = ∑ _x∈U\B,Seven.weight (nbr G w W) (nbr G w L) (f w+nbr G w U) := by
            apply sum_congr rfl; intro x xm
            change Seven.weight _ _ (_+((U.erase x).filter _).card)=_
            rw [er,erase_eq_of_not_mem (mem_sdiff.mp xm).2,sb]
         _ = _ := by simp
  have valB : (∑ x∈B,h x)=B.card*Seven.weight (nbr G w W) (nbr G w L) (f w+(nbr G w U-1)) := by
    calc _ = ∑ _x∈B,Seven.weight (nbr G w W) (nbr G w L) (f w+(nbr G w U-1)) := by
            apply sum_congr rfl; intro x xm
            change Seven.weight _ _ (_+((U.erase x).filter _).card)=_
            rw [er,card_erase_of_mem xm,sb]
         _ = _ := by simp
  rw [←eq,valA,valB,card_sdiff sub,us,sb]
  exact le_of_eq (Nat.add_comm ..)

/-- Pool ranks skip triangle scores two and three, realized by the two cubics. -/
theorem ranks {S : Finset V} (sz : S.card=25) (fi : Function.Injective (trianglesAt G))
    (scores : ∀ v∈S,trianglesAt G v=1 ∨ 4≤trianglesAt G v) :
    ∃ r : V→ℕ,(∀ v∈S,r v<25 ∧ mark (r v)≤trianglesAt G v) ∧
      (∑ v∈S,row (r v))+2*153340=7551356 := by
  classical
  let g (v : V) := if trianglesAt G v=1 then 1 else trianglesAt G v-2
  have inj : Set.InjOn g (S:Set V) := by
    intro v vm w wm eq
    have := scores v vm; have := scores w wm
    unfold g at eq; apply fi; split_ifs at eq <;> omega
  have pos (v : V) (vm : v∈S) : 1≤g v := by have := scores v vm; unfold g; split_ifs <;> omega
  refine ⟨rank S g,?_,?_⟩
  · intro v vm
    have valid := mem_image_of_mem (rank S g) vm
    rw [rank_range S g inj,sz,mem_range] at valid
    refine ⟨valid,?_⟩
    have h := rank_lower S g inj 1 pos vm
    have := scores v vm
    change 1+rank S g v≤(if trianglesAt G v=1 then 1 else trianglesAt G v-2) at h
    unfold mark; split_ifs at * <;> omega
  · rw [sum_by_rank S g inj row,sz]; exact table.2.2.1

end Graffiti384b.OneCommon
#print axioms Graffiti384b.OneCommon.table
#print axioms Graffiti384b.OneCommon.four_fibers
#print axioms Graffiti384b.OneCommon.ranks
