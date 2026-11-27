import PrincipalRank
import LeafStructure

namespace CazenaveRank
open scoped BigOperators
set_option autoImplicit false

/-- The order-two connected adjacency matrix has independent columns. -/
theorem rank_order_two {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hc : G.Connected)
    (hn : Fintype.card V = 2) : columnRank (G.adjMatrix ℝ) = 2 := by
  classical
  have hp := positive_of_connected G hc (by omega)
  have hd (v : V) : G.degree v = 1 := by
    have h := hp v
    have hh := G.degree_lt_card_verts v
    omega
  have hli : LinearIndependent ℝ (G.adjMatrix ℝ).col := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    intro i
    obtain ⟨j,hij⟩ := (G.degree_pos_iff_exists_adj i).mp (hp i)
    have hiji : i ∈ G.neighborFinset j := (G.mem_neighborFinset j i).2 hij.symm
    have hj (v : V) (hv : G.Adj j v) : v = i :=
      (Finset.card_le_one_iff.mp (show (G.neighborFinset j).card ≤ 1 from by
        simp [G.card_neighborFinset_eq_degree,hd])) ((G.mem_neighborFinset j v).mpr hv) hiji
    have h := congrFun hg j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.col_apply, Pi.zero_apply] at h
    have hh : ∑ v, g v * (G.adjMatrix ℝ) j v = g i := by
      rw [Finset.sum_eq_single i]
      · simp [SimpleGraph.adjMatrix_apply, hij.symm]
      · intro v _ hv
        have hh' : ¬ G.Adj j v := fun had => hv (hj v had)
        simp [SimpleGraph.adjMatrix_apply,hh']
      · simp
    rw [hh] at h
    exact h
  unfold columnRank
  rw [Module.finrank_eq_card_basis (Basis.span hli), hn]

#print axioms rank_order_two
end CazenaveRank
