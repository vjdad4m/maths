import AdjacentCutFiveMetric189

namespace Graffiti189LongestPath.CrossSaturation.FiveAdjacent
open SimpleGraph SimpleGraph.Walk Finset
open private CutGraph Shore shore_closed shore_disjoint from AdjacentCutFiveActual189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

/-- Distance through the better of two adjacent cut endpoints: the
extra edge is charged precisely when the strictly nearer endpoints
on the two shores differ. -/
theorem min_two_terminals
    (x₀ x₁ y₀ y₁ : ℕ)
    (a : x₀ ≤ x₁+1) (b : x₁ ≤ x₀+1) (c : y₀ ≤ y₁+1) (d : y₁ ≤ y₀+1) :
    min (x₀+y₀) (x₁+y₁) = min x₀ x₁ + min y₀ y₁ +
      (if (x₀<x₁ ∧ y₁<y₀) ∨ (x₁<x₀ ∧ y₀<y₁) then 1 else 0) := by
  by_cases xl : x₀<x₁ <;> by_cases xr : x₁<x₀ <;>
    by_cases yl : y₀<y₁ <;> by_cases yr : y₁<y₀ <;>
    simp [xl,xr,yl,yr] <;> omega

theorem foreign_distance_by_nearer_endpoint (hc : G.Connected) (ab : G.Adj a b)
    {C D : (CutGraph (G := G) a b).ConnectedComponent} (ne : C≠D)
    {x y : V} (xc : x∈Shore C) (yd : y∈Shore D) :
    G.dist x y = depth G a b x + depth G a b y +
      (if (G.dist a x < G.dist b x ∧ G.dist b y < G.dist a y) ∨
          (G.dist b x < G.dist a x ∧ G.dist a y < G.dist b y) then 1 else 0) := by
  have yn : y∉Shore C := fun h=>disjoint_left.mp (shore_disjoint ne) h yd
  rw [cross_metric (Shore C) hc xc yn (shore_closed C),
    dist_comm (G:=G) (u:=x) (v:=a),dist_comm (G:=G) (u:=x) (v:=b)]
  unfold depth
  apply min_two_terminals
  · have z := hc.dist_triangle (u:=a) (v:=b) (w:=x)
    rw [dist_eq_one_iff_adj.mpr ab] at z
    omega
  · have z := hc.dist_triangle (u:=b) (v:=a) (w:=x)
    rw [dist_eq_one_iff_adj.mpr ab.symm] at z
    omega
  · have z := hc.dist_triangle (u:=a) (v:=b) (w:=y)
    rw [dist_eq_one_iff_adj.mpr ab] at z
    omega
  · have z := hc.dist_triangle (u:=b) (v:=a) (w:=y)
    rw [dist_eq_one_iff_adj.mpr ab.symm] at z
    omega

#print axioms foreign_distance_by_nearer_endpoint
end Graffiti189LongestPath.CrossSaturation.FiveAdjacent
