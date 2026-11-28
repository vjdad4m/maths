import DiversityElevenPendantResidual384b
import DiversityElevenPendantCubic384b

namespace Graffiti384b.DiversityEleven
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Any surviving pendant board has internal minimum degree three,
without any connectivity assumption on the ambient graph or the board. -/
theorem eleven_pendant_board_min_degree (sup : Supported G) (t : (types G).card=11)
    (nine : (high G).card=9) (q : (nonleaves G).card=11) (bad : bound G<gamma G)
    {e f a : V} (ah : a∈high G) (low : nonleaves G \ high G={e,f})
    (en : G.neighborFinset e={f,a}) (fn : G.neighborFinset f={e,a}) :
    ∀ v∈(high G).erase a, 3≤nbr G v ((high G).erase a) := by
  rcases split_profile G sup t bad with ⟨qq,_⟩|⟨_,scores,mins,_⟩
  · omega
  · intro v vB
    have loc := (pendant_board_local G sup ah low en fn vB).2
    have big : 3≤G.degree v := (mem_filter.mp (mem_erase.mp vB).2).2
    have two : 2≤nbr G v ((high G).erase a) := by
      split at loc <;> omega
    by_contra! small
    have ex := exact_of_pendant_board_degree_two G finite_six_selector sup t nine ah low en fn
      vB (by omega) scores mins
    exact (not_le_of_gt bad) ex

theorem residual_eleven_ten_or_dense_pendant (t : (types G).card=11) (bad : bound G<gamma G) :
    ∃ (J : SimpleGraph V) (dec : DecidableRel J.Adj),
      letI := dec
      J ≤ G ∧ Supported J ∧ (∀ v,trianglesAt J v=trianglesAt G v) ∧
        types J=types G ∧ bound J<gamma J ∧ (high J).card=9 ∧
        ((nonleaves J).card=10 ∨
          ((nonleaves J).card=11 ∧ ∃ e f a, e≠f ∧ a∈high J ∧
            nonleaves J \ high J={e,f} ∧
            J.neighborFinset e={f,a} ∧ J.neighborFinset f={e,a} ∧
            ∀ v∈(high J).erase a, 3≤nbr J v ((high J).erase a))) := by
  obtain ⟨J,dec,sub,sup,sc,tp,jbad,nine,rest⟩ := residual_eleven_ten_or_pendant G t bad
  letI := dec
  refine ⟨J,dec,sub,sup,sc,tp,jbad,nine,?_⟩
  rcases rest with h|⟨q,e,f,a,ef,ah,low,en,fn⟩
  · exact Or.inl h
  · exact Or.inr ⟨q,e,f,a,ef,ah,low,en,fn,
      eleven_pendant_board_min_degree J sup (by rwa [tp]) nine q jbad ah low en fn⟩

#print axioms eleven_pendant_board_min_degree
#print axioms residual_eleven_ten_or_dense_pendant
end Graffiti384b.DiversityEleven
