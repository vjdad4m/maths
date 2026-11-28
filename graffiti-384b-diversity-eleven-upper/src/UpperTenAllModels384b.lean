import Mathlib.Tactic.FinCases
import UpperTenData0384b
import UpperTenData1384b
import UpperTenData2384b
import UpperTenData3384b

namespace Graffiti384b.DiversityEleven.CutTen
open Finset
theorem all_models (k : Fin 4) (m : Nat) (hm : m∈cuts k) (bits : Nat→Bool)
    (ad : Admissible (withBits (staticMotif k) bits) m) : ∃ D,Cover (withBits (staticMotif k) bits) D := by
  fin_cases k
  · change m ∈ ({307,355,403,419} : Finset Nat) at hm
    simp only [mem_insert,mem_singleton] at hm
    rcases hm with rfl|rfl|rfl|rfl
    · exact t0m307_cover bits ad
    · exact t0m355_cover bits ad
    · exact t0m403_cover bits ad
    · exact t0m419_cover bits ad
  · change m ∈ ({181,213,229,403,419,451} : Finset Nat) at hm
    simp only [mem_insert,mem_singleton] at hm
    rcases hm with rfl|rfl|rfl|rfl|rfl|rfl
    · exact t1m181_cover bits ad
    · exact t1m213_cover bits ad
    · exact t1m229_cover bits ad
    · exact t1m403_cover bits ad
    · exact t1m419_cover bits ad
    · exact t1m451_cover bits ad
  · change m ∈ ({181,229,403,419} : Finset Nat) at hm
    simp only [mem_insert,mem_singleton] at hm
    rcases hm with rfl|rfl|rfl|rfl
    · exact t2m181_cover bits ad
    · exact t2m229_cover bits ad
    · exact t2m403_cover bits ad
    · exact t2m419_cover bits ad
  · change m ∈ ({121,211,213,227,229} : Finset Nat) at hm
    simp only [mem_insert,mem_singleton] at hm
    rcases hm with rfl|rfl|rfl|rfl|rfl
    · exact t3m121_cover bits ad
    · exact t3m211_cover bits ad
    · exact t3m213_cover bits ad
    · exact t3m227_cover bits ad
    · exact t3m229_cover bits ad

#print axioms all_models
end Graffiti384b.DiversityEleven.CutTen
