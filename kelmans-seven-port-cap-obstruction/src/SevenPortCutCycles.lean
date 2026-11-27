import SevenPortObstruction

namespace KelmansCactus.AtomicBridge.SevenPortObstruction
open Finset

private def cycleTable : Array (Array (List Point × List Point)) := #[
  #[([9,13,10,16],[8,17,18]),([9,13,10,16],[8,15,14,17]),([11,14,17],[8,15,9,13,10,16])],
  #[([10,12,16],[8,15,9,13,11,17]),([9,13,10,16],[8,12,17]),([8,12,10,13,9,15],[11,17,18])],
  #[([7,12,8,15,14],[11,17,18]),([7,12,8,16],[11,14,15,17]),([8,15,17],[7,12,10,16])],
  #[([10,13,16],[7,12,8,17,11,14]),([7,12,8,16],[11,13,17]),([7,12,10,13,11,14],[8,17,18])],
  #[([7,12,8,15,14],[9,17,18]),([7,12,8,16],[9,15,14,17]),([7,14,17],[8,12,10,16])],
  #[([10,13,16],[7,12,8,15,9,17]),([7,12,8,16],[9,13,17]),([8,12,10,13,9,15],[7,17,18])],
  #[([9,13,10,16,11,14,15],[7,17,18]),([9,13,10,16],[7,14,15,17]),([9,15,17],[7,14,11,13,10,16])],
  #[([10,12,16],[7,14,11,13,9,17]),([9,13,10,16],[7,12,17]),([7,12,10,13,11,14],[9,17,18])]]

private def cycles (i : Ear) (l : Layout) : List Point × List Point :=
  ((cycleTable[i.val]?.getD #[])[l.val]?.getD ([],[]))

/-- A distinct cyclic list in the requested shore using only listed edges. -/
def CycleOn (S : Finset Point) (E : List (Point×Point)) (c : List Point) : Prop :=
  3 ≤ c.length ∧ c.Nodup ∧ (∀ v ∈ c,v ∈ S) ∧
    (c ++ c.take 1).Chain' (fun a b => (a,b) ∈ E ∨ (b,a) ∈ E)

instance (S : Finset Point) (E : List (Point×Point)) (c : List Point) :
    Decidable (CycleOn S E c) := by unfold CycleOn; infer_instance

set_option maxRecDepth 10000 in
private theorem table_valid (i : Ear) (l : Layout) :
    CycleOn (shore i l).toFinset (capEdges i l) (cycles i l).1 ∧
    CycleOn (other i l) (capEdges i l) (cycles i l).2 := by
  fin_cases i <;> fin_cases l <;> decide

/-- Both shores of each checked cut contain an explicit cycle. -/
theorem each_cut_is_cyclic (i : Ear) (l : Layout) :
    ∃ left right : List Point,
      CycleOn (shore i l).toFinset (capEdges i l) left ∧
      CycleOn (other i l) (capEdges i l) right :=
  ⟨(cycles i l).1,(cycles i l).2,table_valid i l⟩

#print axioms each_cut_is_cyclic
end KelmansCactus.AtomicBridge.SevenPortObstruction
