import FourRingRootSlots

namespace KelmansCactus.FourRingCutChoices
open FourRingBudget

def diff (a b : Bool) : ℕ := if a=b then 0 else 1

/-- The cost of extending a four-pole partition across the two
adjacent cap roots, counting only edges incident to a root. -/
def extensionCost (p : Slot→Bool) (a b : Bool) : ℕ :=
  diff a (p (false,false)) + diff a (p (false,true)) +
    diff b (p (true,false)) + diff b (p (true,true)) + diff a b

/-- Every cut in a two-root-deleted cell extends to its cap at
additional cost at most two, independent of the port colors. -/
theorem extend_with_at_most_two (p : Slot→Bool) :
    ∃ a b,extensionCost p a b≤2 := by
  exact (show ∀ s : Slot→Bool, ∃ a b,extensionCost s a b≤2 from by decide) p

#print axioms extend_with_at_most_two
end KelmansCactus.FourRingCutChoices
