import Mathlib.Combinatorics.SimpleGraph.Path

namespace KelmansCactus.AtomicBridge.RemoteLadderNoDiagonal
open SimpleGraph
variable {n : ℕ}

abbrev V (n : ℕ) := Fin n × Bool

def railGraph (n : ℕ) : SimpleGraph (V n) where
  Adj x y := (x.1=y.1 ∧ x.2≠y.2) ∨
    (x.2=y.2 ∧ (x.1.val+1=y.1.val ∨ y.1.val+1=x.1.val))
  symm := by
    rintro x y (⟨col,rail⟩|⟨rail,h|h⟩)
    · exact Or.inl ⟨col.symm,Ne.symm rail⟩
    · exact Or.inr ⟨rail.symm,Or.inr h⟩
    · exact Or.inr ⟨rail.symm,Or.inl h⟩
  loopless := by
    rintro x (⟨_,e⟩|⟨_,h|h⟩)
    · exact e rfl
    all_goals omega

theorem step_column {x y : V n} (e : (railGraph n).Adj x y) :
    y.1.val ≤ x.1.val+1 := by
  rcases e with ⟨l,_⟩|⟨_,h|h⟩
  · rw [l]
    omega
  · omega
  · omega

/-- Any left-to-right walk in a ladder visits every intervening column. -/
theorem hits_column {x y : V n} (w : (railGraph n).Walk x y) (c : ℕ)
    (left : x.1.val ≤ c) (right : c≤y.1.val) :
    ∃ z∈w.support,z.1.val=c := by
  induction w with
  | @nil x =>
    exact ⟨x,SimpleGraph.Walk.start_mem_support _,by omega⟩
  | @cons x z y e W ih =>
    by_cases same : x.1.val=c
    · exact ⟨x,SimpleGraph.Walk.start_mem_support _,same⟩
    · have le : z.1.val≤c := by have q := step_column e; omega
      obtain ⟨u,um,uc⟩ := ih le right
      exact ⟨u,List.mem_cons_of_mem _ um,uc⟩

theorem consumes_vertical_pair {x y : V n} (w : (railGraph n).Walk x y)
    (different : x.2≠y.2) :
    ∃ u∈w.support,∃ v∈w.support,u.1=v.1 ∧ u.2≠v.2 := by
  induction w with
  | nil => exact (different rfl).elim
  | @cons x z y e W ih =>
    by_cases rail : x.2=z.2
    · obtain ⟨u,um,v,vm,c,r⟩ := ih (fun e=>different (rail.trans e))
      exact ⟨u,List.mem_cons_of_mem _ um,v,List.mem_cons_of_mem _ vm,c,r⟩
    · have col : x.1=z.1 := by
        rcases e with h|h
        · exact h.1
        · exact (rail h.1).elim
      exact ⟨x,SimpleGraph.Walk.start_mem_support _,z,
        List.mem_cons_of_mem _ (SimpleGraph.Walk.start_mem_support _),col,rail⟩

/-- Two vertex-disjoint diagonally linking walks are impossible in a two-row
ladder exterior. The first rail switch occupies both vertices of a column
that the second left-to-right walk must visit. No planarity axiom is needed. -/
theorem no_disjoint_diagonal {a b c d : V n}
    (A : (railGraph n).Walk a b) (B : (railGraph n).Walk c d)
    (hi : a.2≠b.2) (start : c.1.val=0) (finish : d.1.val+1=n)
    (disjoint : ∀ z,z∈A.support → z∉B.support) :
    False := by
  obtain ⟨u,um,v,vm,col,rail⟩ := consumes_vertical_pair A hi
  have lu : c.1.val≤u.1.val := by omega
  have ru : u.1.val≤d.1.val := by have bound := u.1.isLt; omega
  obtain ⟨z,zm,colz⟩ := hits_column B u.1.val lu ru
  have zcol : z.1=u.1 := Fin.ext colz
  have railOptions : z.2=u.2 ∨ z.2=v.2 := by
    rcases e : z.2 <;> rcases e' : u.2 <;> rcases e'' : v.2 <;> simp_all
  rcases railOptions with zu|zv
  · have eq : z=u := Prod.ext zcol zu
    exact disjoint u um (eq ▸ zm)
  · have eq : z=v := Prod.ext (zcol.trans col) zv
    exact disjoint v vm (eq ▸ zm)

#print axioms no_disjoint_diagonal
end KelmansCactus.AtomicBridge.RemoteLadderNoDiagonal
