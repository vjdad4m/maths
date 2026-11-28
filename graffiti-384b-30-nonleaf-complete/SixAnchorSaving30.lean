import EarTotal30
namespace Graffiti384b.EarMix.Layout
open Finset SimpleGraph Thin28 HighSquare28 JointRank
open private Repair.triangles_le_choose from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] (M : Layout G)

include M in
theorem saving : gamma G≤15 := by
  classical
  let r := rank M.H (trianglesAt G)
  let pay := M.total (hit G M.W) 9 8
  let rebate := M.total (gain G M.W) 9 8
  have rankInfo {w : V} (wm : w∈M.H) : r w<27 ∧ r w+2≤trianglesAt G w := by
    have index := mem_image_of_mem (rank M.H (trianglesAt G)) wm
    rw [rank_range _ _ M.inj,M.size,mem_range] at index
    exact ⟨index,by simpa [r,Nat.add_comm] using rank_lower M.H (trianglesAt G) M.inj 2 M.rich wm⟩
  have ext (w : V) (wm : w∈M.W) : pay w≤row (r w)+rebate w := by
    obtain ⟨rr,lo⟩ := rankInfo (M.wh wm)
    let d := nbr G w M.W
    let a := nbr G w M.A
    let b := nbr G w M.B
    let c := nbr G w M.C
    have da := (pool_degree G wm).trans_le M.ws.le
    have aa : a≤2 := (card_filter_le ..).trans M.asz.le
    have bb : b≤2 := (card_filter_le ..).trans M.bsz.le
    have cc : c≤2 := (card_filter_le ..).trans M.csz.le
    have degree : G.degree w=d+(a+b+c) := (M.exterior_degree wm).trans (M.whigh w)
    have cap := Repair.triangles_le_choose G w
    rw [degree] at cap
    have numeric := rows.1 ⟨_,rr⟩ ⟨d,da⟩ ⟨a,Nat.lt_succ_of_le aa⟩ ⟨b,Nat.lt_succ_of_le bb⟩ ⟨c,Nat.lt_succ_of_le cc⟩ (lo.trans cap)
    change (r w+2<(d+(a+b+c)).choose 2 → exterior d a b c 9 8≤row (r w)) ∧
      exterior d a b c 9 8+min allSelected (exterior d a b c 8 7)≤row (r w)+allSelected at numeric
    have price := M.outside_cost wm 9 8
    change pay w≤exterior d a b c 9 8 at price
    by_cases sat : trianglesAt G w=(G.degree w).choose 2
    · have credit := M.activation wm sat
      have sub := M.outside_cost wm 8 7
      change M.total (hit G M.W) 8 7 w≤exterior d a b c 8 7 at sub
      change allSelected≤rebate w+M.total (hit G M.W) 8 7 w at credit
      omega
    · rw [degree] at sat
      have small := numeric.1 (lo.trans_lt (Nat.lt_of_le_of_ne cap sat))
      omega
  have sideRow (N : Layout G) {w : V} (wm : w∈N.A) (eqH : N.H=M.H) :
      N.total (hit G N.W) 9 8 w+175032≤row (r w) := by
    obtain ⟨rr,lo⟩ := rankInfo (eqH ▸ N.ah wm)
    let d := nbr G w N.W
    let a := nbr G w N.A
    let b := nbr G w N.B
    let c := nbr G w N.C
    have da : d≤21 := (card_filter_le ..).trans N.ws.le
    have aa : a≤1 := by
      have sub : N.A.filter (G.Adj w)⊆N.A.erase w := fun _ h =>
        mem_erase.mpr ⟨(mem_filter.mp h).2.ne.symm,(mem_filter.mp h).1⟩
      have lim := card_le_card sub
      rwa [card_erase_of_mem wm,N.asz] at lim
    have bb : b≤2 := (card_filter_le ..).trans N.bsz.le
    have cc : c≤2 := (card_filter_le ..).trans N.csz.le
    have cap := N.side_score wm
    rw [N.whigh] at cap
    have num := rows.2.1 ⟨_,rr⟩ ⟨d,Nat.lt_succ_of_le da⟩ ⟨a,Nat.lt_succ_of_le aa⟩
      ⟨b,Nat.lt_succ_of_le bb⟩ ⟨c,Nat.lt_succ_of_le cc⟩ (lo.trans cap)
    exact (Nat.add_le_add_right (N.anchor_cost wm) _).trans num
  let B := M.A∪(M.B∪M.C)
  have bs : B.card=6 := by
    rw [show B=M.A∪(M.B∪M.C) from rfl,card_union_of_disjoint (disjoint_union_right.mpr ⟨M.ab,M.ca.symm⟩),
      card_union_of_disjoint M.bc,M.asz,M.bsz,M.csz]
  have side (w : V) (wm : w∈B) : pay w+175032≤row (r w) := by
    rcases mem_union.mp wm with a|rest
    · exact sideRow M a rfl
    change M.total (hit G M.W) 9 8 w+175032≤_
    rw [M.rotate]
    rcases mem_union.mp rest with b|c
    · exact sideRow M.rot b rfl
    rw [M.rot.rotate]; exact sideRow M.rot.rot c rfl
  have exteriorSum := sum_le_sum ext
  have sideSum := sum_le_sum side
  rw [sum_add_distrib] at exteriorSum sideSum
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id,bs] at sideSum
  have wb : Disjoint M.W B := disjoint_union_right.mpr ⟨M.wa,disjoint_union_right.mpr ⟨M.wb,M.wc⟩⟩
  have total {F : V→ℕ} : (∑w∈M.W,F w)+(∑w∈B,F w)=∑w∈M.H,F w := by
    rw [←sum_union wb,M.part]
  have rcost := sum_by_rank M.H (trianglesAt G) M.inj row
  rw [M.size,rows.2.2] at rcost
  change (∑w∈M.H,row (r w))=15220634 at rcost
  have rankTotal := (total (F:=fun w => row (r w))).trans rcost
  have all := total (F:=pay)
  have paid : (∑w∈M.H,pay w)=∑w,pay w := sum_subset (subset_univ _) (fun w _ h => M.ear_zero h)
  have gains : (∑w∈M.W,rebate w)≤∑w,rebate w := sum_le_sum_of_subset (subset_univ _)
  apply Nat.le_of_not_gt; intro bad
  have needed := M.lower bad
  change 14447790+(∑w,rebate w)≤∑w,pay w at needed
  omega
end Graffiti384b.EarMix.Layout
#print axioms Graffiti384b.EarMix.Layout.saving
