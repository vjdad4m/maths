import FiniteLayout

namespace Graffiti199Depleted.WiderOmission

open CompactOmission (SixTree)

structure TreeClause (n : ℕ) where
  domain : ℕ
  value : ℕ
  order : Fin 6 → Fin n

def TreeClause.Valid {n : ℕ} (p : Pattern n) (c : TreeClause n) : Prop :=
  SixTree (p.edge c.value) c.order ∧ ∀ i j, p.known c.domain (c.order i) (c.order j) = true

instance {n : ℕ} (p : Pattern n) (c : TreeClause n) : Decidable (c.Valid p) := by
  unfold TreeClause.Valid
  infer_instance

def TreeClause.Matches {n : ℕ} (c : TreeClause n) (dom val : ℕ) : Prop :=
  dom &&& c.domain = c.domain ∧ val &&& c.domain = c.value

instance {n : ℕ} (c : TreeClause n) (dom val : ℕ) : Decidable (c.Matches dom val) := by
  unfold TreeClause.Matches
  infer_instance

theorem TreeClause.sound {n : ℕ} {p : Pattern n} {c : TreeClause n}
    {row dom val : ℕ} (valid : c.Valid p) (a : Agree row dom val) (match' : c.Matches dom val) :
    SixTree (p.edge row) c.order := by
  have aa : Agree row c.domain c.value := by
    intro k hk
    have hdom := congrArg (fun w : ℕ => w.testBit k) match'.1
    have hval := congrArg (fun w : ℕ => w.testBit k) match'.2
    exact (a k (by simpa [Nat.testBit_and,hk] using hdom)).trans
      (by simpa [Nat.testBit_and,hk] using hval)
  have eq (i j : Fin 6) := edge_agree p aa (valid.2 i j)
  refine ⟨valid.1.1,fun i hi => ?_⟩
  obtain ⟨j,e,lt,unique⟩ := valid.1.2 i hi
  exact ⟨j,(eq i j).trans e,lt,fun k hk lk => unique k ((eq i k).symm.trans hk) lk⟩

def ClauseOrRow {n : ℕ} (d : Family n) (cs : List (TreeClause (n+1))) (good : List ℕ)
    (dom val tag : ℕ) : Prop :=
  if h : tag < cs.length then (cs.get ⟨tag,h⟩).Matches dom val
  else FullyKnown d good dom val (tag-cs.length)

instance {n : ℕ} (d : Family n) (cs : List (TreeClause (n+1))) (good : List ℕ)
    (dom val tag : ℕ) : Decidable (ClauseOrRow d cs good dom val tag) := by
  unfold ClauseOrRow
  split <;> infer_instance

theorem classified_with_clauses {n : ℕ} {d : Family n} {cs : List (TreeClause (n+1))}
    {good : List ℕ} {C : Cover (n+1)}
    (hcs : ∀ i : Fin cs.length, (cs.get i).Valid d.pattern)
    (h : C.Valid d.pattern (ClauseOrRow d cs good) 0 0) (row : ℕ) :
    (∃ T, SixTree (d.pattern.edge row) T) ∨
      ∃ tag ∈ good, ∀ i j, d.pattern.edge row i j = d.pattern.edge tag i j := by
  rcases Cover.start h row with tree|⟨dom,v,t,a,checked⟩
  · exact Or.inl tree
  · by_cases ht : t < cs.length
    · simp only [ClauseOrRow,dif_pos ht] at checked
      exact Or.inl ⟨_,(TreeClause.sound (hcs ⟨t,ht⟩) a checked)⟩
    · simp only [ClauseOrRow,dif_neg ht] at checked
      obtain ⟨tagOk,e,kn⟩ := checked
      exact Or.inr ⟨t-cs.length,tagOk,fun i j => (edge_agree d.pattern a (kn i j)).trans
        (congrArg (fun mask => d.pattern.edge mask i j) e)⟩

end Graffiti199Depleted.WiderOmission
