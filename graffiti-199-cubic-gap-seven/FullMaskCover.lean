import ClauseCover

namespace Graffiti199Depleted.WiderOmission

open CompactOmission (SixTree)

def MaskOrClause {n : ℕ} (d : Family n) (cs : List (TreeClause (n+1))) (good : List ℕ)
    (dom val tag : ℕ) : Prop :=
  if h : tag < cs.length then (cs.get ⟨tag,h⟩).Matches dom val
  else tag-cs.length ∈ good ∧ val = tag-cs.length ∧ dom = 2^d.choices.length - 1

instance decidableMaskOrClause {n : ℕ} (d : Family n) (cs : List (TreeClause (n+1))) (good : List ℕ)
    (dom val tag : ℕ) : Decidable (MaskOrClause d cs good dom val tag) := by
  if h : tag < cs.length then
    exact decidable_of_iff ((cs.get ⟨tag,h⟩).Matches dom val) (by simp [MaskOrClause,h])
  else
    exact decidable_of_iff (tag-cs.length ∈ good ∧ val = tag-cs.length ∧ dom = 2^d.choices.length - 1)
      (by simp [MaskOrClause,h])

private theorem all_known {n : ℕ} (d : Family n) (i j : Fin (n+1)) :
    d.pattern.known (2^d.choices.length - 1) i j = true := by
  letI : BEq (Fin (n+1) × Fin (n+1)) := instBEqOfDecidableEq
  by_cases h : d.choices.idxOf (min i j,max i j) < d.choices.length
  · simp [Pattern.known,Family.pattern,h]
  · simp [Pattern.known,Family.pattern,h]

theorem classified_with_full_mask {n : ℕ} {d : Family n} {cs : List (TreeClause (n+1))}
    {good : List ℕ} {C : Cover (n+1)}
    (hcs : ∀ i : Fin cs.length, (cs.get i).Valid d.pattern)
    (h : C.Valid d.pattern (MaskOrClause d cs good) 0 0) (row : ℕ) :
    (∃ T, SixTree (d.pattern.edge row) T) ∨
      ∃ tag ∈ good, ∀ i j, d.pattern.edge row i j = d.pattern.edge tag i j := by
  rcases Cover.start h row with tree|⟨dom,v,t,a,checked⟩
  · exact Or.inl tree
  · by_cases ht : t < cs.length
    · simp only [MaskOrClause,dif_pos ht] at checked
      exact Or.inl ⟨_,TreeClause.sound (hcs ⟨t,ht⟩) a checked⟩
    · simp only [MaskOrClause,dif_neg ht] at checked
      obtain ⟨tagOk,e,hd⟩ := checked
      subst dom
      exact Or.inr ⟨t-cs.length,tagOk,fun i j => (edge_agree d.pattern a (all_known d i j)).trans
        (congrArg (fun mask => d.pattern.edge mask i j) e)⟩

end Graffiti199Depleted.WiderOmission
