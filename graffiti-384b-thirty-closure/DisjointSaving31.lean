import DisjointBudget31
import DisjointRepair31

namespace Graffiti384b.Disjoint30
open Finset SimpleGraph JointRank
open Graffiti384b.OneCommon (mark)
open private ThreeChoice.balance from ThreeBudget33
open private Repair.nbr_add from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem ranks {S : Finset V} (sz : S.card=28) (fi : Function.Injective (trianglesAt G))
    (scores : ∀ v∈S,trianglesAt G v=1 ∨ 4≤trianglesAt G v) :
    ∃ r : V→ℕ,(∀ v∈S,r v<28 ∧ mark (r v)≤trianglesAt G v) ∧
      (∑ v∈S,row (r v))=9217200 := by
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
  · rw [sum_by_rank S g inj row,sz]; exact table.2.2.2.1

namespace Board
variable {G} (M : Board G)

private theorem coverage_rank (n : Fintype.card V=30) (pos : ∀ v,0<trianglesAt G v)
    (fi : Function.Injective (trianglesAt G)) :
    ∃ r : V→ℕ,(∀ v∈M.W∪M.B,r v<28 ∧ mark (r v)≤trianglesAt G v) ∧
      (∑ v∈M.W,row (r v))+(∑ v∈M.B,row (r v))=9217200 := by
  have dis : Disjoint M.W M.B := disjoint_left.mpr (fun v wm => ((M.outside v).mp wm).2.2)
  have size : (M.W∪M.B).card=28 := by rw [card_union_of_disjoint dis,M.pool_size n,M.bc]
  have ui : M.u∉M.B := by simp [B,U,L,(show ¬G.Adj M.s M.u from fun h => M.sep h.symm)]
  have si : M.s∉M.B := by simp [B,U,L,M.sep]
  have no (v : V) (vm : v∈M.W∪M.B) : v≠M.u ∧ v≠M.s := by
    rcases mem_union.mp vm with w|b
    · exact ⟨((M.outside v).mp w).1,((M.outside v).mp w).2.1⟩
    · exact ⟨fun h => ui (h ▸ b),fun h => si (h ▸ b)⟩
  have scores (v : V) (vm : v∈M.W∪M.B) : trianglesAt G v=1 ∨ 4≤trianglesAt G v := by
    obtain ⟨u,s⟩ := no v vm
    have a : trianglesAt G v≠2 := fun h => u (fi (h.trans M.su.symm))
    have b : trianglesAt G v≠3 := fun h => s (fi (h.trans M.ss.symm))
    have p := pos v; omega
  obtain ⟨r,valid,budget⟩ := ranks G size fi scores
  rw [sum_union dis] at budget
  exact ⟨r,valid,budget⟩

/-- Nine choices of four pins use eight more vertices from the exterior.
At least one of these trials needs at most two repairs. -/
theorem saving (n : Fintype.card V=30) (pos : ∀ v,0<trianglesAt G v)
    (fi : Function.Injective (trianglesAt G)) (cover : ∀ C,G.IsNClique 5 C → 3≤(C∩M.B).card) :
    gamma G≤14 := by
  classical
  let K := M.W.powersetCard 8
  let bad (x y w : V) := (K.filter (fun k => w∈M.failed x y k)).card
  let add (x y : V) := (K.filter (fun k => x∈M.extra x y k)).card
  let fp (x : V) := if x∈M.U then ∑ y∈M.L,add x y else 0
  have ws := M.pool_size n
  obtain ⟨us,ls⟩ := M.sizes
  obtain ⟨r,valid,budget⟩ := M.coverage_rank n pos fi
  have exterior (w : V) (wm : w∈M.W) :
      (∑ x∈M.U,∑ y∈M.L,bad x y w)+price*nbr G w M.B≤row (r w) := by
    obtain ⟨rr,markle⟩ := valid w (mem_union_left _ wm)
    let b := nbr G w M.W
    let i := nbr G w M.U
    let j := nbr G w M.L
    have sub : M.W.filter (G.Adj w)⊆M.W.erase w := fun v vm => mem_erase.mpr ⟨(mem_filter.mp vm).2.ne.symm,(mem_filter.mp vm).1⟩
    have bb := card_le_card sub
    rw [card_erase_of_mem wm,ws] at bb
    change b≤22-1 at bb
    have ii : i≤3 := (card_filter_le ..).trans us.le
    have jj : j≤3 := (card_filter_le ..).trans ls.le
    obtain ⟨plain,cap⟩ := M.pool_score wm cover
    have a := table.1 ⟨r w,rr⟩ ⟨b,by omega⟩ ⟨i,by omega⟩ ⟨j,by omega⟩
      (markle.trans plain) (fun low small => markle.trans (cap low small))
    have rot : (∑ x∈M.U,∑ y∈M.L,bad x y w)≤rotation b 0 i j := by
      simpa only [bad,K,failed,M.pin_count,Nat.zero_add] using nine_fibers G us ls ws wm (fun _ => 0)
    have inc : nbr G w M.B=i+j := Repair.nbr_add G w M.dis
    rw [inc]; exact (Nat.add_le_add_right rot _).trans a
  have boundary (x : V) (xm : x∈M.B) : fp x+anchorAllowance≤row (r x)+price*nbr G x M.W := by
    obtain ⟨rr,markle⟩ := valid x (mem_union_right _ xm)
    have bb : nbr G x M.W≤22 := (card_filter_le ..).trans ws.le
    have ord := table.2.1 ⟨r x,rr⟩ ⟨nbr G x M.W,by omega⟩ (markle.trans (M.anchor_score xm))
    by_cases xu : x∈M.U
    · simp only [fp,if_pos xu]
      rcases M.extra_bound ws xu with none|⟨jl,score,small⟩
      · change (∑ y∈M.L,add x y)=0 at none
        rw [none,Nat.zero_add]; exact ord
      · have cap := table.2.2.1 ⟨r x,rr⟩ ⟨nbr G x M.W,by omega⟩ ⟨nbr G x M.L,by omega⟩ (markle.trans score)
        change (∑ y∈M.L,add x y)≤_ at small
        rw [Nat.add_comm]; exact (Nat.add_le_add_left small anchorAllowance).trans cap
    · simpa [fp,xu] using ord
  have flip (T : Finset V) (F : Finset V → Finset V) (sub : ∀ k∈K,F k⊆T) :
      (∑ k∈K,(F k).card)=∑ w∈T,(K.filter (fun k => w∈F k)).card := by
    calc _ = ∑ k∈K,∑ w∈T,if w∈F k then 1 else 0 := by
            apply sum_congr rfl; intro k km; simp [sum_boole,filter_mem_eq_inter,inter_eq_right.mpr (sub k km)]
         _ = _ := by rw [sum_comm]; simp [sum_boole]
  have extId (x y : V) : (∑ k∈K,(M.failed x y k).card)=∑ w∈M.W,bad x y w :=
    flip M.W (M.failed x y) (fun _ _ => (filter_subset ..).trans sdiff_subset)
  have addId (x y : V) : (∑ k∈K,(M.extra x y k).card)=add x y := by
    simpa [add] using flip {x} (M.extra x y) (fun _ _ => filter_subset ..)
  have swap : (∑ x∈M.U,∑ y∈M.L,∑ w∈M.W,bad x y w)=∑ w∈M.W,∑ x∈M.U,∑ y∈M.L,bad x y w := by
    calc _ = ∑ x∈M.U,∑ w∈M.W,∑ y∈M.L,bad x y w := sum_congr rfl (fun _ _ => sum_comm)
         _ = _ := sum_comm
  by_contra! no
  have lower (x : V) (xm : x∈M.U) (y : V) (ym : y∈M.L) (k : Finset V) (km : k∈K) :
      3≤(M.failed x y k).card+(M.extra x y k).card := by
    have h := M.trial xm ym km; omega
  have necessary := sum_le_sum (s:=M.U) (fun x xm => sum_le_sum (s:=M.L) (fun y ym => sum_le_sum (s:=K) (lower x xm y ym)))
  simp_rw [sum_add_distrib,extId,addId] at necessary
  rw [swap] at necessary
  have kc : K.card=(22:ℕ).choose 8 := by rw [show K=M.W.powersetCard 8 from rfl,card_powersetCard,ws]
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id,us,ls,kc] at necessary

  have eSum := sum_le_sum exterior
  have aSum := sum_le_sum boundary
  rw [sum_add_distrib,←mul_sum] at eSum
  rw [sum_add_distrib,sum_const,nsmul_eq_mul,Nat.cast_id,M.bc,sum_add_distrib,←mul_sum] at aSum
  rw [ThreeChoice.balance G M.B M.W] at eSum
  have fpeq : (∑ x∈M.B,fp x)=∑ x∈M.U,∑ y∈M.L,add x y := by
    rw [B,sum_union (show Disjoint M.U M.L from M.dis)]
    have lhs : (∑ x∈M.U,fp x)=(∑ x∈M.U,∑ y∈M.L,add x y) := sum_congr rfl (fun x xm => if_pos xm)
    have rhs : (∑ x∈M.L,fp x)=0 := sum_eq_zero (fun x xm => if_neg (fun xu => disjoint_left.mp M.dis xu xm))
    rw [lhs,rhs,Nat.add_zero]
  rw [fpeq] at aSum
  have strict := table.2.2.2.2
  omega

end Board
end Graffiti384b.Disjoint30
#print axioms Graffiti384b.Disjoint30.Board.saving
