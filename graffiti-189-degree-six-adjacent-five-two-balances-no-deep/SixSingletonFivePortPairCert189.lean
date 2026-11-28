import SixSingletonPortCertificates189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix.PortCertificates

abbrev CommonPairModel (C : Fin 3 → Fin 3 → Bool) (Z W : Fin 3 → Bool) : Prop :=
  ∀ i : Fin 3, 3≤marks (C i 0)+marks (C i 1)+marks (C i 2)+marks (Z i)+marks (W i)

abbrev ThreeOrder (i j k : Fin 3) := i≠j ∧ i≠k ∧ j≠k

abbrev CommonEarly (C : Fin 3 → Fin 3 → Bool) (Z : Fin 3 → Bool) : Prop :=
  ∃ i j k : Fin 3, ThreeOrder i j k ∧ Z i=true ∧ C i j=true ∧ C j k=true

abbrev CommonFinish (C : Fin 3 → Fin 3 → Bool) (Z W : Fin 3 → Bool) (T : Bool) : Prop :=
  ∃ i j k : Fin 3, ThreeOrder i j k ∧ Z i=true ∧
    ((C i j=true ∧ C j k=true ∧ W k=true ∧ T=true) ∨
     (W i=true ∧ W j=true ∧ C j k=true) ∨
     (C i j=true ∧ W j=true ∧ W k=true))

private instance (C : Fin 3 → Fin 3 → Bool) (Z W : Fin 3 → Bool) (T : Bool) :
    Decidable (CommonFinish C Z W T) := by
  unfold CommonFinish ThreeOrder
  infer_instance

set_option maxHeartbeats 100000000
set_option maxRecDepth 32768
set_option synthInstance.maxHeartbeats 1000000

theorem common_early_certificate (a b c z0 z1 z2 : Bool) :
    ∀ w0 w1 w2 : Bool,
    CommonPairModel (rows33 a b c) (row3 z0 z1 z2) (row3 w0 w1 w2) →
    (z0=true ∨ z1=true ∨ z2=true) → CommonEarly (rows33 a b c) (row3 z0 z1 z2) := by
  cases a <;> cases b <;> cases c <;> cases z0 <;> revert z1 z2 <;> decide

theorem common_finish_certificate (a b c z0 z1 z2 : Bool) :
    ∀ w0 w1 w2 t : Bool,
    CommonPairModel (rows33 a b c) (row3 z0 z1 z2) (row3 w0 w1 w2) →
    (z0=true ∨ z1=true ∨ z2=true) →
    (1≤marks w0 + marks w1 + marks w2) →
    ((2≤marks w0 + marks w1 + marks w2) ∨ t=true) →
    CommonFinish (rows33 a b c) (row3 z0 z1 z2) (row3 w0 w1 w2) t := by
  cases a <;> cases b <;> cases c <;> cases z0 <;> revert z1 z2 <;> decide

#print axioms common_early_certificate
#print axioms common_finish_certificate
end Graffiti189LongestPath.CrossSaturation.ThresholdSix.PortCertificates
