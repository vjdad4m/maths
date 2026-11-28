import SixSingletonFivePortPairCert189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix.PortCertificates

abbrev OnlyCommonExit (C : Fin 3→Fin 3→Bool) (Z W : Fin 3→Bool) : Prop :=
  ∃ i j k : Fin 3,ThreeOrder i j k ∧ Z i=true ∧
      ((W i=true ∧ W j=true ∧ C j k=true) ∨ (C i j=true ∧ W j=true ∧ W k=true))

private instance (C : Fin 3→Fin 3→Bool) (Z W : Fin 3→Bool) :
    Decidable (OnlyCommonExit C Z W) := by
  unfold OnlyCommonExit ThreeOrder
  infer_instance

set_option maxHeartbeats 100000000
set_option maxRecDepth 32768
set_option synthInstance.maxHeartbeats 1000000

theorem tiny_common_exit_certificate (a b c : Bool) :
    ∀ z0 z1 z2 w0 w1 w2 : Bool,
      ((a=true ∨ b=true) ∧ (a=true ∨ c=true) ∧ (b=true ∨ c=true)) →
      2≤marks z0+marks z1+marks z2 → 2≤marks w0+marks w1+marks w2 →
      OnlyCommonExit (rows33 a b c) (row3 z0 z1 z2) (row3 w0 w1 w2) := by
  cases a <;> cases b <;> cases c <;> decide

#print axioms tiny_common_exit_certificate
end Graffiti189LongestPath.CrossSaturation.ThresholdSix.PortCertificates
