import Components189
import Path189
import ThreeCut189
namespace Issue189
set_option maxHeartbeats 12000000
set_option maxRecDepth 100000
theorem diam_three : (∀ u v : V, G.dist u v ≤ 3) ∧ G.dist 3 21 = 3 := by
  simp only [dist_eq]; decide
theorem has_triangle : G.Adj 0 1 ∧ G.Adj 1 2 ∧ G.Adj 2 0 := by decide
/-- A graph satisfying the #189 premise with a unique minimum separator, whose
deletion leaves three connected components. A direct Hamiltonian path is supplied
so this cannot be mistaken for a counterexample to #189. -/
theorem regression :
    Fintype.card V = 34 ∧ G.Connected ∧
    (∀ u : V, 15 ≤ G.degree u ∧ ev u ≤ 16) ∧
    (G.degree 21 = 15 ∧ G.degree 22 = 15 ∧ ev 0 = 16) ∧
    xyZ.card = 13 ∧ ¬ (H xyZ).Preconnected ∧
    (∀ s : Finset V, s.card ≤ 13 → ¬ (H s).Preconnected → s = xyZ) ∧
    Nat.card (H xyZ).ConnectedComponent = 3 ∧
    fullPath.IsPath ∧ (∀ v : V, fullPath.support.count v = 1) :=
  ⟨by decide, connected, hypotheses.1, hypotheses.2, weights.2.2.2,
    cut_is_disconnected, no_smaller_or_other_minimum, three_components,
    fullPath_isPath, fullPath_hamiltonian⟩
#print axioms regression
#print axioms diam_three
end Issue189
