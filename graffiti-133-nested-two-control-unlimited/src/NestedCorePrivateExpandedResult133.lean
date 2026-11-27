import NestedCorePrivateSingleRows133
import NestedCorePrivateDualRows133

namespace Graffiti133ExpandedPrivate
open SimpleGraph Graffiti133 Graffiti133PrivateGeneric
variable {V : Type*} {G : SimpleGraph V}

theorem no_single_case_model
    (m : Bool) (c : Fin 2) (i : Fin 7) (wide opp : Bool) (nonprivate : wide=true ∨ opp=true)
    (f : Fin 19→V) (fi : Function.Injective f) (h4 : FourCycleFree G)
    (h9 : ¬∃ p : Fin 9→V,InducedPath G p) : ¬Fit G f (singleCase m c i wide opp) := by
  intro hf
  obtain ⟨t,ok⟩ := single_case_all_rows m c i wide opp nonprivate
  exact checked_sound h4 h9 fi _ hf t [] (by intro q qm; cases qm) ok

theorem no_dual_single_case_model
    (m : Bool) (i : Fin 7) (f : Fin 19→V) (fi : Function.Injective f) (h4 : FourCycleFree G)
    (h9 : ¬∃ p : Fin 9→V,InducedPath G p) : ¬Fit G f (dualSingleCase m i) := by
  intro hf
  obtain ⟨t,ok⟩ := dual_single_all_rows m i
  exact checked_sound h4 h9 fi _ hf t [] (by intro q qm; cases qm) ok

theorem no_dual_adjacent_case_model
    (m : Bool) (i : Fin 7) (f : Fin 20→V) (fi : Function.Injective f) (h4 : FourCycleFree G)
    (h9 : ¬∃ p : Fin 9→V,InducedPath G p) : ¬Fit G f (dualAdjacentCase m i) := by
  intro hf
  obtain ⟨t,ok⟩ := dual_adjacent_all_rows m i
  exact checked_sound h4 h9 fi _ hf t [] (by intro q qm; cases qm) ok

#print axioms no_single_case_model
#print axioms no_dual_single_case_model
#print axioms no_dual_adjacent_case_model
end Graffiti133ExpandedPrivate
