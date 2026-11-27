import Final
import TwinRandic

namespace CazenaveRank
open scoped BigOperators
set_option autoImplicit false

private theorem leaf_deletion : LeafRandicDecrease := by
  intro V _ _ G _ u v a hc huv hau hav hdu _
  exact randicRows_remove_twin_leaf G hc huv hau hav hdu

/-- The second inequality of Conjecture 6(iv), Cazenave, arXiv:2611.03879v1:
R(G) ≥ 1 + (3/2)(√rank(A) − √2) for every connected simple graph of order ≥2. -/
theorem cazenave_six_iv_rank
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 2 ≤ Fintype.card V) (hc : G.Connected) :
    1+(3/2)*(Real.sqrt (columnRank (G.adjMatrix ℝ))-Real.sqrt 2) ≤
      ∑ e ∈ G.edgeFinset, conventionalWeight G e :=
  rank_bound_assembly_unordered leaf_deletion G hn hc

/-- Equality occurs precisely when the connected graph has order two, i.e. K₂. -/
theorem cazenave_six_iv_rank_equality
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 2 ≤ Fintype.card V) (hc : G.Connected) :
    (∑ e ∈ G.edgeFinset, conventionalWeight G e) =
      1+(3/2)*(Real.sqrt (columnRank (G.adjMatrix ℝ))-Real.sqrt 2) ↔
      Fintype.card V = 2 := by
  rw [← randic_eq_unordered]
  exact rank_equality_assembly leaf_deletion G hn hc

#print axioms cazenave_six_iv_rank
#print axioms cazenave_six_iv_rank_equality
end CazenaveRank
