import DiversityElevenExactThreePendant384b
import DiversityElevenPendantTagResidual384b

namespace Graffiti384b.DiversityEleven
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Residual supported order-eleven branch after the exact three-tag
closure: pendant triangle, dense connected board, and four to six tags. -/
def FourToSixPendant : Prop :=
  (nonleaves G).card=11 ∧
    ∃ e f a, e≠f ∧ a∈high G ∧ nonleaves G \ high G={e,f} ∧
      G.neighborFinset e={f,a} ∧ G.neighborFinset f={e,a} ∧
      let B := (high G).erase a
      let Z := B.filter (fun v => ¬G.Adj v a)
      (∀ v∈B,3≤nbr G v B) ∧ 4≤Z.card ∧ Z.card≤6 ∧
      ∀ X Y : Finset V, X.Nonempty → Y.Nonempty → Disjoint X Y → X∪Y=B →
        ∃ x∈X,∃ y∈Y,G.Adj x y

theorem residual_eleven_ten_or_four_to_six_tags (t : (types G).card=11) (bad : bound G<gamma G) :
    ∃ (J : SimpleGraph V) (dec : DecidableRel J.Adj),
      letI := dec
      J ≤ G ∧ Supported J ∧ (∀ v,trianglesAt J v=trianglesAt G v) ∧
        types J=types G ∧ bound J<gamma J ∧ (high J).card=9 ∧
        ((nonleaves J).card=10 ∨ FourToSixPendant J) := by
  obtain ⟨J,dec,sub,sup,sc,tp,jbad,nine,rest⟩ := residual_eleven_ten_or_three_to_six_tags G t bad
  letI := dec
  have tj : (types J).card=11 := by rwa [tp]
  refine ⟨J,dec,sub,sup,sc,tp,jbad,nine,?_⟩
  rcases rest with q|⟨q,e,f,a,ef,ah,low,en,fn,dense,zmin,zmax,cross⟩
  · exact Or.inl q
  rcases split_profile J sup tj jbad with ⟨qq,_⟩|⟨_,scores,mins,_⟩
  · omega
  · refine Or.inr ⟨q,e,f,a,ef,ah,low,en,fn,dense,?_,zmax,cross⟩
    by_contra! small
    exact (not_le_of_gt jbad) (exact_pendant_three_tags J sup tj nine ah low en fn scores mins dense (by omega))

#print axioms residual_eleven_ten_or_four_to_six_tags
end Graffiti384b.DiversityEleven
