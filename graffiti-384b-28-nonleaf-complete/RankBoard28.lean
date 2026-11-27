import SixRows28

namespace Graffiti384b.FiveBoard28
open Finset SimpleGraph JointRank
open Graffiti384b.Port28 (mark)
open private ThreeChoice.balance from ThreeBudget33
open private Repair.nbr_add from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem ranks {S : Finset V} (sz : S.card=26) (fi : Function.Injective (trianglesAt G))
    (scores : ∀ v∈S,trianglesAt G v=1 ∨ 4≤trianglesAt G v) :
    ∃ r : V→ℕ,(∀ v∈S,r v<26 ∧ mark (r v)≤trianglesAt G v) ∧
      (∑ v∈S,row (r v))=11198043 := by
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

namespace Board
open private ForcedCubics.third_contact from SharedSaving33
variable {G} (M : Board G)
theorem one_U {x : V} (xm : x∈M.U) : 1≤nbr G x (M.U.erase x) := by
  have hc : (M.U.erase x).card=2 := by rw [card_erase_of_mem xm,M.sizes.1]
  obtain ⟨p,pm,q,qm,pq⟩ := one_lt_card.mp (show 1<(M.U.erase x).card by omega)
  obtain ⟨px,pu⟩ := mem_erase.mp pm
  obtain ⟨qx,qu⟩ := mem_erase.mp qm
  rcases ForcedCubics.third_contact G M.du M.su.ge pq ((G.mem_neighborFinset ..).mp pu)
    ((G.mem_neighborFinset ..).mp qu) ((G.mem_neighborFinset ..).mp xm) px.symm qx.symm with edge|edge
  · exact card_pos.mpr ⟨p,mem_filter.mpr ⟨pm,edge⟩⟩
  · exact card_pos.mpr ⟨q,mem_filter.mpr ⟨qm,edge⟩⟩



theorem coverage_rank (n : Fintype.card V=28) (pos : ∀ v,0<trianglesAt G v)
    (fi : Function.Injective (trianglesAt G)) :
    ∃ r : V→ℕ,(∀ v∈M.W∪M.B,r v<26 ∧ mark (r v)≤trianglesAt G v) ∧
      (∑ v∈M.W,row (r v))+(∑ v∈M.B,row (r v))=11198043 := by
  have dis : Disjoint M.W M.B := disjoint_left.mpr (fun v wm => ((M.outside v).mp wm).2.2)
  have size : (M.W∪M.B).card=26 := by rw [card_union_of_disjoint dis,M.pool_size n,M.bc]
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

end Board
end Graffiti384b.FiveBoard28
#print axioms Graffiti384b.FiveBoard28.Board.coverage_rank
