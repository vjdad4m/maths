import AdjacentCutFiveThreeSingleton189

namespace Graffiti189LongestPath.CrossSaturation.FiveAdjacent
open SimpleGraph SimpleGraph.Walk Finset
open private CutGraph Shore from AdjacentCutFiveActual189
open private Vis from AdjacentCutFiveComponents189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

/-- If a globally minimum shore among adjacent genuine two-cuts has
two visible vertices and any interior, these ports are a genuinely
nonadjacent two-cut. No dispatcher or traceability assumption enters. -/
theorem nonadjacent_cut_of_two_visible_minimal_adjacent_shore
    (C : (CutGraph (G := G) a b).ConnectedComponent)
    (minimal : ∀ (u v : V), G.Adj u v →
      2 ≤ Nat.card (CutGraph (G := G) u v).ConnectedComponent →
      ∀ E : (CutGraph (G := G) u v).ConnectedComponent, (Shore C).card ≤ (Shore E).card)
    (ports : (Vis C).card=2) (large : 2<(Shore C).card) :
    ∃ u v : V, u≠v ∧ ¬G.Adj u v ∧
      2 ≤ Nat.card (CutGraph (G := G) u v).ConnectedComponent := by
  obtain ⟨u,v,uv,_,cut,E,_,sm⟩ := actual_cut_of_two_visible_shore C ports large
  exact ⟨u,v,uv,fun adj => (not_lt_of_ge (minimal u v adj cut E)) sm,cut⟩

#print axioms nonadjacent_cut_of_two_visible_minimal_adjacent_shore
end Graffiti189LongestPath.CrossSaturation.FiveAdjacent
