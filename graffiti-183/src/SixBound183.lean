import BlockTrim183

namespace Graffiti183.Exceptional
open SimpleGraph Finset Short177

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem bipartite_at_least_six {v w : V} (p : SixPattern G v w) :
    6 ≤ Graffiti183.bipartiteNumber G := by
  classical
  let L := [w,p.q,p.a,v,p.b,p.p]
  let A : Finset V := {w,p.a,p.b}
  let B : Finset V := {p.q,v,p.p}
  let T := L.toFinset
  have ht : T.card = 6 := by
    change L.toFinset.card = 6
    rw [List.toFinset_card_of_nodup p.all_distinct]
    rfl
  have hcover : A ∪ B = T := by
    ext x
    simp [A,B,T,L,or_assoc,or_left_comm,or_comm]
  have hiA : Indep G A := by
    intro x hx y hy hn he
    simp only [A,mem_insert,mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    · exact hn rfl
    · exact p.n_aw he.symm
    · exact p.n_wb he
    · exact p.n_aw he
    · exact hn rfl
    · exact p.n_ab he
    · exact p.n_wb he.symm
    · exact p.n_ab he.symm
    · exact hn rfl
  have hiB : Indep G B := by
    intro x hx y hy hn he
    simp only [B,mem_insert,mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    · exact hn rfl
    · exact p.n_vq he.symm
    · exact p.n_qp he
    · exact p.n_vq he
    · exact hn rfl
    · exact p.n_vp he
    · exact p.n_qp he.symm
    · exact p.n_vp he.symm
    · exact hn rfl
  have hd : Disjoint A B := by
    have hh := p.all_distinct
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or,
      List.nodup_nil, not_false_eq_true, and_true] at hh
    rcases hh with ⟨⟨wq,wa,wv,wb,wp⟩,⟨qa,qv,qb,qp⟩,⟨av,ab,ap⟩,⟨vb,vp⟩,bp⟩
    apply Finset.disjoint_left.mpr
    intro x hx hy
    simp only [A,B,mem_insert,mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with h | h | h <;>
      first | exact wq h | exact wv h | exact wp h | exact qa h.symm |
        exact av h | exact ap h | exact qb h.symm | exact vb h.symm | exact bp h
  have hT : T.card ≤ Short177.bipartiteNum G := by
    unfold Short177.bipartiteNum
    exact le_sup (s := univ.filter (Short177.TwoColor G)) (f := Finset.card)
      (mem_filter.mpr ⟨mem_univ _,A,B,hd,hcover,hiA,hiB⟩)
  rw [←ht]
  exact hT.trans (Graffiti185.Reuse.bipartite_bridge G)

theorem conjecture183_of_six_pattern_of_leaf_bound {v w : V} (p : SixPattern G v w)
    (hc : G.Connected) (hL : Fintype.card V ≤ Graffiti183.maxLeaves G + 4) : Claim183 G := by
  have hb := bipartite_at_least_six p
  have hm := Graffiti183.metric_upper_bound hc
  unfold Claim183
  omega

#print axioms conjecture183_of_six_pattern_of_leaf_bound
end Graffiti183.Exceptional
