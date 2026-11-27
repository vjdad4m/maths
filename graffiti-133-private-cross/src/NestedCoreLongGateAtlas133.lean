import C7CoreOrder133
import C7MultiWeightedLocal133
import Mathlib.Tactic.FinCases

namespace Graffiti133NestedLongGates
open SimpleGraph Finset Graffiti133 Graffiti133NoFive Graffiti133MultiC7
  Graffiti133CoreSeven
open scoped Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

def Separate (p q : Fin 14) : Prop := ((profileContacts p)∩(profileContacts q)).card≤1
instance : DecidableRel Separate := fun p q=>inferInstanceAs (Decidable (((profileContacts p)∩(profileContacts q)).card≤1))

def ProfileCoverage (p q r s : Fin 14) (i : Fin 7) : Prop :=
  (∀ j : Fin 7,farSites i j →
    ((i∈profileContacts p ∧ j∈profileContacts p) ∨ (i∈profileContacts q ∧ j∈profileContacts q) ∨
      (i∈profileContacts r ∧ j∈profileContacts r) ∨ (i∈profileContacts s ∧ j∈profileContacts s))) ∧
  (∃ j : Fin 7,j∈profileContacts p ∧ (j=i ∨ Cyclic i j)) ∧
  (∃ j : Fin 7,j∈profileContacts q ∧ (j=i ∨ Cyclic i j))

instance (p q r s : Fin 14) (i : Fin 7) : Decidable (ProfileCoverage p q r s i) := inferInstanceAs
  (Decidable ((∀ j : Fin 7,farSites i j →
    ((i∈profileContacts p ∧ j∈profileContacts p) ∨ (i∈profileContacts q ∧ j∈profileContacts q) ∨
      (i∈profileContacts r ∧ j∈profileContacts r) ∨ (i∈profileContacts s ∧ j∈profileContacts s))) ∧
  (∃ j : Fin 7,j∈profileContacts p ∧ (j=i ∨ Cyclic i j)) ∧
  (∃ j : Fin 7,j∈profileContacts q ∧ (j=i ∨ Cyclic i j))))

theorem four_long_gate_profile_center (p : Fin 14) : ∀ q r s : Fin 14,
    profileOK p q → Separate p q → Separate p r → Separate p s → Separate q r →
      Separate q s → Separate r s → ∃ i : Fin 7,ProfileCoverage p q r s i := by
  fin_cases p <;> decide

theorem allowed_nonempty_profile_type :
    ∀ A : Finset (Fin 7),C4Allowed A → A.Nonempty →
      (∃ i : Fin 7,A={i}) ∨ (∃ i : Fin 7,A={i,i+1}) ∨ ∃ p : Fin 14,A=profileContacts p := by
  decide

#print axioms four_long_gate_profile_center
#print axioms allowed_nonempty_profile_type
end Graffiti133NestedLongGates
