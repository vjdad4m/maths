import TwinReduction
import Flanks23
import Flanks24

open private exterior_off_of_three from CoreTransfer

namespace Graffiti199Depleted.WiderOmission

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}
variable [DecidableEq V] [DecidableRel G.Adj] [Fintype V]

/-- A certified uniform contact on two adjacent core labels turns them
into true twins in the whole graph. Each exterior contact is checked
on the smaller labelled core, regardless of the order of the graph. -/
theorem twins_of_uniform_flank {n : ℕ} {e : Fin (n+1) → Fin (n+1) → Bool}
    {mate : Fin (n+1)} (rules : FlankRules n e mate) {f : Fin (n+1) ↪ V}
    (budget : Catalogue.treeNumber G ≤ 5)
    (chart : ∀ i j, G.Adj (f i) (f j) ↔ e i j = true)
    (outside : ∀ w, (∀ i, w ≠ f i) → ¬ G.Adj w (f (Fin.last n)) ∧ ¬ G.Adj w (f mate))
    {i j : Fin (n+1)} (edge : e i j = true)
    (core : ∀ k, k ≠ i → k ≠ j → e i k = e j k)
    (profiles : ∀ m ∈ rules.profiles, touch m i = touch m j) :
    AdjacentTwins G (f i) (f j) := by
  refine ⟨(chart _ _).mpr edge,?_⟩
  intro w wi wj
  by_cases inside : ∃ k, f k = w
  · obtain ⟨k,rfl⟩ := inside
    have ki : k ≠ i := fun eq => wi (congrArg f eq)
    have kj : k ≠ j := fun eq => wj (congrArg f eq)
    rw [chart,chart,core k ki kj]
  · have dis : ∀ k, w ≠ f k := fun k eq => inside ⟨k,eq.symm⟩
    obtain ⟨m,hm,h⟩ := external_profile budget rules chart dis
      (outside w dis).1 (outside w dis).2
    rw [G.adj_comm (f i),G.adj_comm (f j),h i,h j,profiles m hm]

omit [DecidableEq V] in
theorem exterior_of_cubic_chart {n : ℕ} {e : Fin (n+1) → Fin (n+1) → Bool}
    (f : Fin (n+1) ↪ V) (chart : ∀ i j, G.Adj (f i) (f j) ↔ e i j = true)
    {u a b c : Fin (n+1)} (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c)
    (d : G.degree (f u) = 3) (ea : e u a = true) (eb : e u b = true) (ec : e u c = true)
    (w : V) (off : ∀ i, w ≠ f i) : ¬ G.Adj w (f u) :=
  exterior_off_of_three off ab ac bc d ((chart _ _).mpr ea) ((chart _ _).mpr eb) ((chart _ _).mpr ec)

/-- Any induced copy of the first residual 2-and-3 core in a graph
with the two specified cubic degrees has true twins at labels 4 and 5. -/
theorem twins_from_23_chart (f : Fin 9 ↪ V) (budget : Catalogue.treeNumber G ≤ 5)
    (chart : ∀ i j, G.Adj (f i) (f j) ↔ edge23 0 253 i j = true)
    (dz : G.degree (f 8) = 3) (dm : G.degree (f 1) = 3) :
    AdjacentTwins G (f 4) (f 5) := by
  apply twins_of_uniform_flank flanks23_0 budget chart
  · intro w off
    exact ⟨exterior_of_cubic_chart f chart (a := 1) (b := 3) (c := 6) (by decide)
      (by decide) (by decide) dz (by decide) (by decide) (by decide) w off,
      exterior_of_cubic_chart f chart (a := 0) (b := 2) (c := 8) (by decide)
        (by decide) (by decide) dm (by decide) (by decide) (by decide) w off⟩
  · decide
  · decide
  · intro m hm
    have cases : m = 0 ∨ m = 120 ∨ m = 201 ∨ m = 204 ∨ m = 205 := by
      simpa [flanks23_0] using hm
    rcases cases with rfl|rfl|rfl|rfl|rfl <;> decide

/-- The corresponding induced 2-and-4 chart when the middle port is cubic. -/
theorem twins_from_24_chart (f : Fin 10 ↪ V) (budget : Catalogue.treeNumber G ≤ 5)
    (chart : ∀ i j, G.Adj (f i) (f j) ↔ edge24 1 7932 i j = true)
    (dz : G.degree (f 9) = 3) (dm : G.degree (f 3) = 3) :
    AdjacentTwins G (f 5) (f 6) := by
  apply twins_of_uniform_flank flanks24_1 budget chart
  · intro w off
    exact ⟨exterior_of_cubic_chart f chart (a := 1) (b := 3) (c := 7) (by decide)
      (by decide) (by decide) dz (by decide) (by decide) (by decide) w off,
      exterior_of_cubic_chart f chart (a := 2) (b := 4) (c := 9) (by decide)
        (by decide) (by decide) dm (by decide) (by decide) (by decide) w off⟩
  · decide
  · decide
  · intro m hm
    have cases : m = 0 ∨ m = 230 ∨ m = 242 ∨ m = 246 ∨ m = 387 := by
      simpa [flanks24_1] using hm
    rcases cases with rfl|rfl|rfl|rfl|rfl <;> decide

#print axioms twins_of_uniform_flank
#print axioms twins_from_23_chart
#print axioms twins_from_24_chart

end Graffiti199Depleted.WiderOmission
