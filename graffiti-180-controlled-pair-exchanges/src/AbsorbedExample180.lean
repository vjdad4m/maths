import AbsorbedGate180
import Example180
set_option warningAsError true
set_option maxHeartbeats 800000
namespace Minimal180.Case12
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 Controlled

/-- In the nonsaturated twelve-vertex example, absorbing the old leaves
0 and 5 makes the contact argument work without naming a returning leaf. -/
theorem from_absorbed_gate :
    FirstForm J U 7 8 1 ∧ ∃ B⊆C.erase 7,B.card=1 ∧
      let L' := (C.erase 7\B)∪{3,11}
      Con G (univ\L') ∧ ∀ q∈L',Dominates G (univ\L') q := by
  let Z : Finset V := {3,11}
  let R := (univ\C)\Z
  let H : Finset V := {4,6,9,10}
  have two : remote J R 8={H} := by
    apply remote_eq_singleton J R {8} H 8 4 (by decide) (by decide) (by decide) (by decide)
    · exact con 8 (fun _ => 0) (by decide) (by decide)
    · exact con 4 (fun i => [88,88,88,88,0,88,2,88,88,1,1,88][i.val]!) (by decide) (by decide)
    · decide
  have empty : demand J R C Z 7=∅ := by
    apply eq_empty_of_forall_not_mem
    intro q h
    obtain ⟨place,nr,nx⟩ := (mem_demand ..).mp h
    rcases (show ∀ i∈C.erase 7∪Z,Dominates J R i ∨ J.Adj i 7 by unfold Dominates; decide) q place with dom|e
    · exact nr dom
    · exact nx e
  have region (P : Finset V) (h : P∈remote J R 8) : ∃ z∈Z,∃ F⊆C.erase 7,
      (∀ i∈P,∀ j∈Z,J.Adj i j → j=z) ∧ (∀ i∈F,∀ j,J.Adj i j → j∈P∪F ∨ j=z) ∧
      (∀ b∈C.erase 7,b∉F → Dominates J P b → J.Adj 7 b) := by
    have eq := mem_singleton.mp (two ▸ h)
    subst P
    refine ⟨11,by decide,{0,5},by decide,by decide,by decide,?_⟩
    unfold Dominates
    decide
  obtain ⟨B,bc,upper,lower,first,con,dom⟩ := controlled_of_absorbed_gates J jc (by decide) 7 8 1
    (by decide) (by decide) (by decide) (by decide) U C Z (by decide) (by rw [old_score]; decide)
    specified_exchange.1 (by decide) (by rw [add_eq]; exact block) empty region
  rw [add_eq] at con dom
  change B.card≤(remote J R 8).card at upper
  rw [two,card_singleton] at upper
  have nZ : Z.card=2 := by decide
  exact ⟨first (by omega),B,bc,by omega,con,dom⟩

#print axioms from_absorbed_gate
end Minimal180.Case12
