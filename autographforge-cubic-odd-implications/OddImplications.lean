import Transfer

namespace CubicBridges1160
open SimpleGraph

/-- A cubic graph can require more cliques than one third its edge count. -/
theorem row3232_false :
    ¬ (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      (1/3 : ℚ) * G.edgeFinset.card < (cliqueCover G : ℚ) →
        ¬ G.IsRegularOfDegree 3) := by
  intro h
  apply (h Vertex graph ?_) cubic
  rw [size_exact, cover_exact]
  norm_num

/-- A cubic graph can require more cliques than its harmonic index. -/
theorem row4862_false :
    ¬ (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      RegularHarmonic595.harmonicIndex G < (cliqueCover G : ℚ) →
        ¬ G.IsRegularOfDegree 3) := by
  intro h
  apply (h Vertex graph ?_) cubic
  rw [harmonic_exact, cover_exact]
  norm_num

#print axioms row3232_false
#print axioms row4862_false
end CubicBridges1160
