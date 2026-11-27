import DepletedBlockAdapter

namespace Graffiti199Depleted

open SimpleGraph

private def orientLoss (k : O) : O → O :=
  match k with
  | 2 => ![0,1,3,2,4,5]
  | 4 => ![1,0,5,4,2,3]
  | 5 => ![1,0,4,5,2,3]
  | _ => id

private theorem orientLoss_cert (k : O) (high : 2 ≤ k.val) :
    Function.Injective (orientLoss k) ∧
      (∀ j : O, (∃ i : O, terminalKept true i = true ∧ orientLoss k i = j) ↔ j ≠ k) ∧
      (∀ i : O, i ∈ ([0,1] : List O) → orientLoss k i ∈ ([0,1] : List O)) ∧
      (∀ a b : O, (a,b) ∈ terminalEdges → terminalHas (orientLoss k a) (orientLoss k b) = true) := by
  revert k
  decide

variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]

/-- A paired block with at most one lost high can be relabelled with the
lost high at label three. The new kept region is exactly the original
paired block with the indicated loss removed. -/
theorem terminal_pair_of_at_most_one_loss (Q : O ↪ V) (lost : Finset O)
    (count : lost.card ≤ 1) (lostHigh : ∀ i ∈ lost, 2 ≤ i.val)
    (edges : ∀ a b, (a,b) ∈ terminalEdges → G.Adj (Q a) (Q b))
    (degree : ∀ i ∈ ([0,1] : List O), G.degree (Q i) = 3) :
    ∃ (loss : Bool) (R : O ↪ V), (loss = true ↔ lost.card = 1) ∧
      terminalRegion R loss = {v | ∃ i : O, i ∉ lost ∧ Q i = v} ∧
      (∀ a b, (a,b) ∈ terminalEdges → G.Adj (R a) (R b)) ∧
      (∀ i ∈ ([0,1] : List O), G.degree (R i) = 3) := by
  by_cases zero : lost.card = 0
  · have empty := Finset.card_eq_zero.mp zero
    refine ⟨false,Q,by simp [zero],?_,edges,degree⟩
    ext v
    simp [terminalRegion,terminalKept,empty]
  · have one : lost.card = 1 := by omega
    obtain ⟨k,unique⟩ := Finset.card_eq_one.mp one
    have kh : 2 ≤ k.val := lostHigh k (by simp [unique])
    obtain ⟨inj,image,lows,allowed⟩ := orientLoss_cert k kh
    let P : O ↪ O := ⟨orientLoss k,inj⟩
    let R := P.trans Q
    refine ⟨true,R,by simp [one],?_,?_,?_⟩
    · ext v
      constructor
      · rintro ⟨i,keep,e⟩
        have off := (image (P i)).mp ⟨i,keep,rfl⟩
        exact ⟨P i,by simpa [unique] using off,e⟩
      · rintro ⟨j,off,e⟩
        obtain ⟨i,keep,ij⟩ := (image j).mpr (by simpa [unique] using off)
        exact ⟨i,keep,(congrArg Q ij).trans e⟩
    · intro a b e
      have match' := allowed a b e
      simp only [terminalHas,Bool.or_eq_true,List.contains_iff_mem] at match'
      exact match'.elim (edges _ _) (fun h => (edges _ _ h).symm)
    · exact fun i hi => degree _ (lows i hi)

#print axioms terminal_pair_of_at_most_one_loss

end Graffiti199Depleted
