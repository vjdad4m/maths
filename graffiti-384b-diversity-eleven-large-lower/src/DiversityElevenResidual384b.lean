import LargeLowerProfile384b
import UpperTenExact384b

namespace Graffiti384b.DiversityEleven
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Any diversity-eleven counterexample has a triangle-supported spanning
subgraph with the same vertex scores, nine high vertices, and between ten
and thirteen nonisolated vertices. -/
theorem residual_eleven (t : (types G).card=11) (bad : bound G<gamma G) :
    ∃ (J : SimpleGraph V) (dec : DecidableRel J.Adj),
      letI := dec
      J ≤ G ∧ Supported J ∧ (∀ v,trianglesAt J v=trianglesAt G v) ∧
        types J=types G ∧ bound J<gamma J ∧ (high J).card=9 ∧
        10≤(nonleaves J).card ∧ (nonleaves J).card≤13 := by
  obtain ⟨J,dec,sub,sup,sc,tp,jbad⟩ := triangle_supported_reduction G t bad
  letI := dec
  have tj : (types J).card=11 := by simpa [tp] using t
  rcases split_profile J sup tj jbad with ⟨_,noEars⟩|⟨nine,_,_,_⟩
  · exact (not_le_of_gt jbad (exact_of_supported_no_ears J sup noEars tj)).elim
  · have mn := (ten_to_fifteen J tj jbad).1
    have mx : (nonleaves J).card≤13 := by
      by_contra! lg
      exact not_le_of_gt jbad (exact_large_lower_profile J sup tj nine (by omega))
    exact ⟨J,dec,sub,sup,sc,tp,jbad,nine,mn,mx⟩

#print axioms residual_eleven
end Graffiti384b.DiversityEleven
