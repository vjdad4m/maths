import SquaredPath

/-! AutoGraphForge physical row 2473, ID 27d9e7c4. -/
namespace MeanDistance2473

open SimpleGraph SquaredPath2039

/-- NetworkX sums shortest-path lengths over all ordered pairs. The zero
diagonal contributes nothing, and the denominator counts distinct pairs. -/
noncomputable def orderedDistanceSum {U : Type*} [Fintype U] (G : SimpleGraph U) : ℕ :=
  ∑ u : U, ∑ v : U, G.dist u v

/-- The catalogue uses this value on connected graphs of order at least two. -/
noncomputable def averageShortestPathLength {U : Type*} [Fintype U] (G : SimpleGraph U) : ℚ :=
  (orderedDistanceSum G : ℚ) / (Fintype.card U * (Fintype.card U - 1) : ℕ)

theorem ordered_sum_exact : orderedDistanceSum graph = 256 := by
  have h : graph.dist = distance := funext (fun u => funext (metric.2 u))
  unfold orderedDistanceSum
  rw [h]
  decide

theorem mean_exact : averageShortestPathLength graph = 128 / 45 := by
  unfold averageShortestPathLength
  rw [ordered_sum_exact,Fintype.card_fin]
  norm_num

/-- On GraphCalc's numerical domain, the catalogue inequality is false. -/
theorem row2473_false : ¬ (∀ (U : Type) [Fintype U] (G : SimpleGraph U) [DecidableRel G.Adj],
    2 ≤ Fintype.card U → G.CliqueFree 4 → ClawFree G → G.Connected →
    averageShortestPathLength G ≤ (7/5 : ℚ) * slater G) := by
  intro claim
  have bound := claim V graph (by decide) k4_free claw_free connected
  rw [mean_exact,slater_exact] at bound
  norm_num at bound

#print axioms ordered_sum_exact
#print axioms mean_exact
#print axioms row2473_false

end MeanDistance2473
