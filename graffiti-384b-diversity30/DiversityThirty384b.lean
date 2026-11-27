import EvenNonleaves384b
import SampleThirty384b

namespace Graffiti384b.Diversity30
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Every finite simple graph with precisely thirty distinct vertex
triangle-incidence counts satisfies the catalogue bound. -/
theorem exact_thirty_types (t : (types G).card=30) : gamma G≤bound G := by
  by_cases many : 30≤(nonleaves G).card
  · exact many_nonleaves G t many
  · exact EvenQuota.exact_of_fewer_nonleaves G (by rw [t]) (by omega)

/-- At every order, fifteen vertices can simultaneously be left outside
a 2-dominating set whenever there are thirty triangle-count types. -/
theorem exists_set (t : (types G).card=30) :
    ∃ D : Finset V,TwoDominates G D ∧ D.card+15≤Fintype.card V := by
  have existsD : {k : ℕ | ∃ D, TwoDominates G D ∧ D.card=k}.Nonempty :=
    ⟨_,univ,by simp [TwoDominates],rfl⟩
  obtain ⟨D,dom,size⟩ := Nat.sInf_mem existsD
  change D.card=gamma G at size
  have enough : (types G).card≤Fintype.card V := (card_image_le (s:=(univ : Finset V))
    (f:=trianglesAt G)).trans_eq card_univ
  have boundG := exact_thirty_types G t
  unfold bound at boundG
  rw [t] at boundG
  exact ⟨D,dom,by omega⟩

end Graffiti384b.Diversity30
#print axioms Graffiti384b.Diversity30.exact_thirty_types
#print axioms Graffiti384b.Diversity30.exists_set
