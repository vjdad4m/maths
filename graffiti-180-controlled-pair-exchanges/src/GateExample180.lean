import SaturatedPair180
import AllTips180
set_option warningAsError true
set_option maxHeartbeats 1000000
namespace Minimal180.Case14
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 Controlled
noncomputable abbrev releases : Finset V := {0,13}

private noncomputable abbrev D3 : Finset V := {4,6,7,8,9,10,11,12}
private noncomputable abbrev H3 : Finset V := {2}
theorem remote3 : remote J ((univ\C3)\releases) 4={H3} := by
  apply remote_eq_singleton J _ D3 H3 4 2 (by decide) (by decide) (by decide) (by decide)
  · exact con 4 (fun i => [88,88,88,88,0,88,1,2,2,4,5,5,3,88][i.val]!) (by decide) (by decide)
  · exact con 2 (fun i => [88,88,0,88,88,88,88,88,88,88,88,88,88,88][i.val]!) (by decide) (by decide)
  · decide

/-- The single-gate theorem constructs the second returned leaf. -/
theorem controlled3 : FirstForm J U 3 4 5 ∧ ∃ b∈C3.erase 3, let L := (C3.erase 3).erase b ∪ releases
    L⊆U\{3,4} ∧ L.card=C3.card ∧ L\C3=releases ∧ C3\L={3,b} ∧
    Con G (univ\L) ∧ ∀ q∈L,Dominates G (univ\L) q := by
  have eq : J⊔SimpleGraph.edge 3 4=G := by exact add_eq
  rw [←eq]
  apply saturated_pair J jc (by decide) 3 4 5 (by decide) (by decide) (by decide) (by decide)
    U C3 releases H3 (by decide) (by rw [old_score]; decide) tip3 (by decide) (by decide)
  · rw [eq]; exact block
  · decide
  · unfold Dominates; decide
  · exact remote3
  · exact ⟨0,by decide,by decide⟩

#print axioms controlled3

private noncomputable abbrev D4 : Finset V := {1,2,3}
private noncomputable abbrev H4 : Finset V := {7,8,9,10,11,12}
theorem remote4 : remote J ((univ\C4)\releases) 3={H4} := by
  apply remote_eq_singleton J _ D4 H4 3 7 (by decide) (by decide) (by decide) (by decide)
  · exact con 1 (fun i => [88,0,1,1,88,88,88,88,88,88,88,88,88,88][i.val]!) (by decide) (by decide)
  · exact con 7 (fun i => [88,88,88,88,88,88,88,0,1,2,3,3,1,88][i.val]!) (by decide) (by decide)
  · decide

/-- The single-gate theorem constructs the second returned leaf. -/
theorem controlled4 : FirstForm J U 4 3 5 ∧ ∃ b∈C4.erase 4, let L := (C4.erase 4).erase b ∪ releases
    L⊆U\{4,3} ∧ L.card=C4.card ∧ L\C4=releases ∧ C4\L={4,b} ∧
    Con G (univ\L) ∧ ∀ q∈L,Dominates G (univ\L) q := by
  have eq : J⊔SimpleGraph.edge 4 3=G := by rw [edge_comm]; exact add_eq
  rw [←eq]
  apply saturated_pair J jc (by decide) 4 3 5 (by decide) (by decide) (by decide) (by decide)
    U C4 releases H4 (by decide) (by rw [old_score]; decide) tip4 (by decide) (by decide)
  · rw [eq]; exact block
  · decide
  · unfold Dominates; decide
  · exact remote4
  · exact ⟨13,by decide,by decide⟩

#print axioms controlled4
end Minimal180.Case14
