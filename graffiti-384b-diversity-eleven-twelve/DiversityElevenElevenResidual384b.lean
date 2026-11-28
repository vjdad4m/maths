import SixUntouchedCover384b
import TwelveSelectorConditional384b

namespace Graffiti384b.DiversityEleven
open Finset SimpleGraph

theorem finite_six_selector : SixSelector :=
  selector_of_packed Graffiti384b.SixUntouched.all_packed

/-- The supported lower profile at order twelve is exact at diversity eleven. -/
theorem exact_twelve_supported {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (sup : Supported G) (t : (types G).card=11)
    (nine : (high G).card=9) (q : (nonleaves G).card=12) :
    gamma G≤bound G :=
  exact_twelve_lower finite_six_selector G sup t nine q

/-- Any diversity-eleven counterexample has a supported spanning
counterexample of nonisolated order 10 or 11, with unchanged scores. -/
theorem residual_eleven_orders_ten_eleven {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : (types G).card=11) (bad : bound G<gamma G) :
    ∃ (J : SimpleGraph V) (dec : DecidableRel J.Adj),
      letI := dec
      J ≤ G ∧ Supported J ∧ (∀ v,trianglesAt J v=trianglesAt G v) ∧
        types J=types G ∧ bound J<gamma J ∧ (high J).card=9 ∧
        10≤(nonleaves J).card ∧ (nonleaves J).card≤11 :=
  residual_eleven_at_most_eleven finite_six_selector G t bad

#print axioms finite_six_selector
#print axioms exact_twelve_supported
#print axioms residual_eleven_orders_ten_eleven
end Graffiti384b.DiversityEleven
