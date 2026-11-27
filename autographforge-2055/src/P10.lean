import Sharpness

namespace PathCycleSharpness
open SimpleGraph Finset
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

abbrev P := pathGraph 10

instance : DecidableRel P.Adj := fun x y => decidable_of_iff
  (x.val+1 = y.val ∨ y.val+1 = x.val) pathGraph_adj.symm

theorem p10_tree : P.IsTree := by
  apply isTree_iff_connected_and_card.mpr
  refine ⟨pathGraph_connected 9,?_⟩
  have degreeSum : ∑ v, P.degree v = 18 := by decide
  have handshake := P.sum_degrees_eq_twice_card_edges
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← P.edgeFinset_card, Fintype.card_fin]
  omega

theorem p10_claw_free : ClawFree P := by
  intro v a b c ha hb hc hab hac hbc
  rw [pathGraph_adj] at ha hb hc
  have distinct {x y : Fin 10} (h : x ≠ y) : x.val ≠ y.val := fun e => h (Fin.ext e)
  have := distinct hab
  have := distinct hac
  have := distinct hbc
  omega

theorem p10_burning : burning P = 4 := by
  let schedule (i : Fin 4) : Fin 10 := if i=0 then 0 else if i=1 then 3 else if i=2 then 7 else 9
  apply burning_certificate P lineDistance
    (metric_certificate lineDistance (by decide) (by decide) (by decide)) 4 schedule
  all_goals decide

theorem p10_slater : slater P = 4 := by
  let l := List.replicate 8 2 ++ [1,1]
  apply slater_certificate P l _ 4 (by decide) (by decide)
  unfold degreesDesc
  rw [Finset.val_univ_fin, Multiset.map_coe, Multiset.coe_sort]
  have eq : (List.finRange 10).map (P.degree ·) = [1,2,2,2,2,2,2,2,2,1] := by decide
  rw [eq]
  simp [List.mergeSort,l]

theorem row2055_equality : 2 ≤ Fintype.card (Fin 10) ∧ ClawFree P ∧ P.IsTree ∧
    (burning P : ℚ) = (1/2 : ℚ) * slater P + 2 := by
  refine ⟨by decide,p10_claw_free,p10_tree,?_⟩
  rw [p10_burning,p10_slater]
  norm_num

#print axioms p10_burning
#print axioms p10_slater
#print axioms row2055_equality

end PathCycleSharpness
