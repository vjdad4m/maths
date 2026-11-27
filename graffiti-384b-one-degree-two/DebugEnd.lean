import PreserveEar
namespace Graffiti384b.QuotaEar
open Finset SimpleGraph LowSample
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
set_option maxHeartbeats 15000
/-- At most one vertex of degree two suffices whenever there are
at least as many nonleaves as distinct triangle counts. -/
theorem few_check (q : (types G).card≤(nonleaves G).card) (few : (twos G).card≤1) :
    gamma G≤bound G := by
  have sub : high G⊆nonleaves G := fun v vm => mem_filter.mpr ⟨mem_univ _,by have := (mem_filter.mp vm).2; omega⟩
  have n : (twos G).card+(high G).card=(nonleaves G).card := card_sdiff_add_card_eq_card sub
  by_cases enough : (types G).card≤(high G).card
  · exact exact_of_high G (by omega)
  exact equal_quota G (by omega) (by omega)

/-- At even diversity the single-ear conclusion holds at every nonleaf quota. -/
theorem even_few_check (even : (types G).card%2=0) (few : (twos G).card≤1) : gamma G≤bound G := by
  by_cases enough : (types G).card≤(nonleaves G).card
  · exact few_check G enough few
  · exact EvenQuota.exact_of_fewer_nonleaves G even (Nat.lt_of_not_ge enough)

end Graffiti384b.QuotaEar
