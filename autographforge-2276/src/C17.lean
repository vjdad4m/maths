import Sharpness

namespace PathCycleSharpness
open SimpleGraph Finset
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

abbrev C := cycleGraph 17

private def cycleDistance (x y : Fin 17) := min (lineDistance x y) (17 - lineDistance x y)

theorem c17_eulerian : Eulerian C :=
  ⟨cycleGraph_connected (n := 16),fun _ => by rw [cycleGraph_degree_three_le]⟩

theorem c17_subcubic : Subcubic C := fun _ => by rw [cycleGraph_degree_three_le]; decide

theorem c17_burning : burning C = 5 := by
  let schedule (i : Fin 5) : Fin 17 :=
    if i=0 then 0 else if i=1 then 1 else if i=2 then 6 else if i=3 then 10 else 12
  apply burning_certificate C cycleDistance
    (metric_certificate cycleDistance (by decide) (by decide) (by decide)) 5 schedule
  all_goals decide

theorem c17_slater : slater C = 6 := by
  let l := List.replicate 17 2
  apply slater_certificate C l _ 6 (by decide) (by decide)
  unfold degreesDesc
  rw [Finset.val_univ_fin, Multiset.map_coe, Multiset.coe_sort]
  have eq : (List.finRange 17).map (C.degree ·) = List.replicate 17 2 := by decide
  rw [eq]
  simp [List.mergeSort,l]

theorem row2276_equality : 2 ≤ Fintype.card (Fin 17) ∧ Eulerian C ∧ Subcubic C ∧
    (burning C : ℚ) = (1/3 : ℚ) * slater C + 3 := by
  refine ⟨by decide,c17_eulerian,c17_subcubic,?_⟩
  rw [c17_burning,c17_slater]
  norm_num

#print axioms c17_burning
#print axioms c17_slater
#print axioms row2276_equality

end PathCycleSharpness
