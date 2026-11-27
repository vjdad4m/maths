import BridgePair180
import AllTips180
set_option warningAsError true
set_option maxHeartbeats 1000000
namespace Minimal180.Case14
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 Controlled

theorem bridge_repair3 : FirstForm J U 3 4 5 ∧ ∃ b∈C3.erase 3,
    let L := (C3.erase 3).erase b ∪ {0,13}
    L⊆U\{3,4} ∧ L.card=C3.card ∧ L\C3={0,13} ∧ C3\L={3,b} ∧
    Con G (univ\L) ∧ ∀ z∈L,Dominates G (univ\L) z := by
  have eq : J⊔SimpleGraph.edge 3 4=G := by exact add_eq
  rw [←eq]
  apply pair_of_bridge_ports J jc (by decide) 3 4 5 0 13 2 10
    (by decide) (by decide) (by decide) (by decide) U C3 (by decide)
    (by rw [old_score]; decide) tip3 (by decide)
  · rw [eq]; exact block
  · decide
  · refine ⟨by decide,(fun i => decide (i∈({0,2}:Finset V))),by decide,?_⟩
    decide
  all_goals decide
#print axioms bridge_repair3

theorem bridge_repair4 : FirstForm J U 4 3 5 ∧ ∃ b∈C4.erase 4,
    let L := (C4.erase 4).erase b ∪ {0,13}
    L⊆U\{4,3} ∧ L.card=C4.card ∧ L\C4={0,13} ∧ C4\L={4,b} ∧
    Con G (univ\L) ∧ ∀ z∈L,Dominates G (univ\L) z := by
  have eq : J⊔SimpleGraph.edge 4 3=G := by rw [edge_comm]; exact add_eq
  rw [←eq]
  apply pair_of_bridge_ports J jc (by decide) 4 3 5 0 13 1 10
    (by decide) (by decide) (by decide) (by decide) U C4 (by decide)
    (by rw [old_score]; decide) tip4 (by decide)
  · rw [eq]; exact block
  · decide
  · refine ⟨by decide,(fun i => decide (i∈({0,1,2,3}:Finset V))),by decide,?_⟩
    decide
  all_goals decide
#print axioms bridge_repair4
end Minimal180.Case14
