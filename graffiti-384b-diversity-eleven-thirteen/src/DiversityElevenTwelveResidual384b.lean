import ThirteenLower384b
import DiversityElevenResidual384b

namespace Graffiti384b.DiversityEleven
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Any diversity-eleven counterexample has nine high vertices and 10–12
nonisolated vertices in a score-preserving supported spanning subgraph. -/
theorem residual_eleven_at_most_twelve (t : (types G).card=11) (bad : bound G<gamma G) :
    ∃ (J : SimpleGraph V) (dec : DecidableRel J.Adj),
      letI := dec
      J ≤ G ∧ Supported J ∧ (∀ v,trianglesAt J v=trianglesAt G v) ∧
        types J=types G ∧ bound J<gamma J ∧ (high J).card=9 ∧
        10≤(nonleaves J).card ∧ (nonleaves J).card≤12 := by
  obtain ⟨J,dec,sub,sup,sc,tp,jbad,nine,mn,mx⟩ := residual_eleven G t bad
  letI := dec
  have tj : (types J).card=11 := by simpa [tp] using t
  have top : (nonleaves J).card≤12 := by
    by_contra! large
    exact not_le_of_gt jbad (exact_thirteen_lower J sup tj nine (by omega))
  exact ⟨J,dec,sub,sup,sc,tp,jbad,nine,mn,top⟩

#print axioms residual_eleven_at_most_twelve
end Graffiti384b.DiversityEleven
