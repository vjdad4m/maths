import RankBound
import LeafStructure

namespace CazenaveRank
open scoped BigOperators
set_option autoImplicit false
set_option linter.unnecessarySimpa false

/-- Every connected graph of order two has one edge of weight one. -/
theorem randic_order_two {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hc : G.Connected)
    (hn : Fintype.card V = 2) : randic G = 1 := by
  have hpos := positive_of_connected G hc (by omega)
  have hdeg (v : V) : G.degree v = 1 := by
    have h := G.degree_lt_card_verts v
    have h' := hpos v
    omega
  have hi (v : V) : (∑ w ∈ G.neighborFinset v,
      (1:ℝ)/(Real.sqrt (G.degree v) * Real.sqrt (G.degree w))) = 1 := by
    simp [hdeg,Finset.sum_const,G.card_neighborFinset_eq_degree]
  unfold randic
  simp_rw [hi,Finset.sum_const,Finset.card_univ,hn,nsmul_eq_mul]
  norm_num

#print axioms randic_order_two
end CazenaveRank
