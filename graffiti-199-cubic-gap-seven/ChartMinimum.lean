import TwinMinimum
import UniformProfiles

namespace Graffiti199Depleted.WiderOmission

open SimpleGraph

universe u
variable {V : Type u} {G : SimpleGraph V}
variable [DecidableEq V] [DecidableRel G.Adj] [Fintype V]

def contactCount {n : ℕ} (p : Fin (n+1) → Bool) : ℕ :=
  (Finset.univ.filter (fun i => p i = true)).card

omit [DecidableEq V] in
theorem contact_count_le_degree {n : ℕ} (f : Fin (n+1) ↪ V) (w : V)
    {p : Fin (n+1) → Bool} (edges : ∀ i, p i = true → G.Adj w (f i)) :
    contactCount p ≤ G.degree w := by
  unfold contactCount
  let S : Finset (Fin (n+1)) := Finset.univ.filter (fun i => p i = true)
  change S.card ≤ G.degree w
  rw [← Finset.card_map f,← G.card_neighborFinset_eq_degree]
  apply Finset.card_le_card
  intro x hx
  obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hx
  exact (G.mem_neighborFinset _ _).mpr (edges _ (Finset.mem_filter.mp hi).2)

theorem common_neighbors_high_of_flank {n : ℕ} {e : Fin (n+1) → Fin (n+1) → Bool}
    {mate : Fin (n+1)} (rules : FlankRules n e mate) {f : Fin (n+1) ↪ V}
    (budget : Catalogue.treeNumber G ≤ 5)
    (chart : ∀ i j, G.Adj (f i) (f j) ↔ e i j = true)
    (outside : ∀ w, (∀ i, w ≠ f i) → ¬ G.Adj w (f (Fin.last n)) ∧ ¬ G.Adj w (f mate))
    {i j : Fin (n+1)}
    (localHigh : ∀ k, k ≠ i → k ≠ j → e k i = true → 4 ≤ contactCount (e k))
    (externalHigh : ∀ m ∈ rules.profiles, touch m i = true →
      4 ≤ contactCount (fun k : Fin (n+1) => touch m k)) :
    ∀ w, G.Adj w (f i) → G.Adj w (f j) → 4 ≤ G.degree w := by
  intro w wi wj
  by_cases inside : ∃ k, f k = w
  · obtain ⟨k,rfl⟩ := inside
    have ki : k ≠ i := fun h => wi.ne (congrArg f h)
    have kj : k ≠ j := fun h => wj.ne (congrArg f h)
    exact (localHigh k ki kj ((chart _ _).mp wi)).trans
      (contact_count_le_degree f _ (fun t ht => (chart _ _).mpr ht))
  · have dis : ∀ k, w ≠ f k := fun k eq => inside ⟨k,eq.symm⟩
    obtain ⟨m,hm,h⟩ := external_profile budget rules chart dis
      (outside w dis).1 (outside w dis).2
    exact (externalHigh m hm ((h i).mp wi)).trans
      (contact_count_le_degree f _ (fun t ht => (h t).mpr ht))

/-- A single embedded residual 2-and-3 chart already forces
traceability under the archived minimum-order hypotheses, regardless
of the order or position of the chart in the original graph. -/
theorem traceable_of_minimum_23_chart (f : Fin 9 ↪ V)
    (chart : ∀ i j, G.Adj (f i) (f j) ↔ edge23 0 253 i j = true)
    (dz : G.degree (f 8) = 3) (dm : G.degree (f 1) = 3)
    (smaller : Catalogue.SmallerAtThree.{u} (Fintype.card V))
    (conn : Catalogue.ConnectivityAtLeast G 3) (cross : CrossingBetweenSurvivingEdges G)
    (budget : Catalogue.treeNumber G ≤ 5) : Catalogue.Traceable G := by
  have order : 5 ≤ Fintype.card V := by
    have h := Fintype.card_le_of_injective f f.injective
    simp only [Fintype.card_fin] at h
    omega
  apply (twins_from_23_chart f budget chart dz dm).traceable_of_minimum smaller conn cross budget order
  apply common_neighbors_high_of_flank flanks23_0 budget chart
  · intro w off
    exact ⟨exterior_of_cubic_chart f chart (a := 1) (b := 3) (c := 6) (by decide)
      (by decide) (by decide) dz (by decide) (by decide) (by decide) w off,
      exterior_of_cubic_chart f chart (a := 0) (b := 2) (c := 8) (by decide)
        (by decide) (by decide) dm (by decide) (by decide) (by decide) w off⟩
  · decide
  · intro m hm
    have cases : m = 0 ∨ m = 120 ∨ m = 201 ∨ m = 204 ∨ m = 205 := by
      simpa [flanks23_0] using hm
    rcases cases with rfl|rfl|rfl|rfl|rfl <;> decide

/-- The corresponding obstruction from the second residual chart,
which names the middle port as the cubic neighbor. -/
theorem traceable_of_minimum_24_chart (f : Fin 10 ↪ V)
    (chart : ∀ i j, G.Adj (f i) (f j) ↔ edge24 1 7932 i j = true)
    (dz : G.degree (f 9) = 3) (dm : G.degree (f 3) = 3)
    (smaller : Catalogue.SmallerAtThree.{u} (Fintype.card V))
    (conn : Catalogue.ConnectivityAtLeast G 3) (cross : CrossingBetweenSurvivingEdges G)
    (budget : Catalogue.treeNumber G ≤ 5) : Catalogue.Traceable G := by
  have order : 5 ≤ Fintype.card V := by
    have h := Fintype.card_le_of_injective f f.injective
    simp only [Fintype.card_fin] at h
    omega
  apply (twins_from_24_chart f budget chart dz dm).traceable_of_minimum smaller conn cross budget order
  apply common_neighbors_high_of_flank flanks24_1 budget chart
  · intro w off
    exact ⟨exterior_of_cubic_chart f chart (a := 1) (b := 3) (c := 7) (by decide)
      (by decide) (by decide) dz (by decide) (by decide) (by decide) w off,
      exterior_of_cubic_chart f chart (a := 2) (b := 4) (c := 9) (by decide)
        (by decide) (by decide) dm (by decide) (by decide) (by decide) w off⟩
  · decide
  · intro m hm
    have cases : m = 0 ∨ m = 230 ∨ m = 242 ∨ m = 246 ∨ m = 387 := by
      simpa [flanks24_1] using hm
    rcases cases with rfl|rfl|rfl|rfl|rfl <;> decide

#print axioms traceable_of_minimum_23_chart
#print axioms traceable_of_minimum_24_chart

end Graffiti199Depleted.WiderOmission
