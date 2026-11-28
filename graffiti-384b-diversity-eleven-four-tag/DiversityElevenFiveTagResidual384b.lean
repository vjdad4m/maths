import DiversityElevenFourTagResidual384b
import DiversityElevenExactFourSelector384b

namespace Graffiti384b.DiversityEleven
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem selector_at_four : EightSelectorAt 4 := by
  intro H dec Z d c m s
  letI := dec
  exact exact_four_selector H Z c d m s

/-- Exact supported-graph closure for the dense board with four tags. -/
theorem exact_pendant_four_tags (sup : Supported G) (t : (types G).card=11)
    (nine : (high G).card=9) {e f a : V} (ah : a∈high G)
    (low : nonleaves G \ high G={e,f})
    (en : G.neighborFinset e={f,a}) (fn : G.neighborFinset f={e,a})
    (scores : Set.InjOn (trianglesAt G) (high G : Set V))
    (mins : ∀ v∈high G, 2≤trianglesAt G v)
    (dense : ∀ v∈(high G).erase a, 3≤nbr G v ((high G).erase a))
    (zc : (((high G).erase a).filter (fun v => ¬G.Adj v a)).card=4) :
    gamma G≤bound G :=
  exact_pendant_selector_at G selector_at_four sup t nine ah low en fn scores mins dense zc

def FiveOrSixPendant : Prop :=
  (nonleaves G).card=11 ∧
    ∃ e f a, e≠f ∧ a∈high G ∧ nonleaves G \ high G={e,f} ∧
      G.neighborFinset e={f,a} ∧ G.neighborFinset f={e,a} ∧
      let B := (high G).erase a
      let Z := B.filter (fun v => ¬G.Adj v a)
      (∀ v∈B,3≤nbr G v B) ∧ 5≤Z.card ∧ Z.card≤6 ∧
      ∀ X Y : Finset V, X.Nonempty → Y.Nonempty → Disjoint X Y → X∪Y=B →
        ∃ x∈X,∃ y∈Y,G.Adj x y

theorem residual_eleven_ten_or_five_six_tags (t : (types G).card=11) (bad : bound G<gamma G) :
    ∃ (J : SimpleGraph V) (dec : DecidableRel J.Adj),
      letI := dec
      J ≤ G ∧ Supported J ∧ (∀ v,trianglesAt J v=trianglesAt G v) ∧
        types J=types G ∧ bound J<gamma J ∧ (high J).card=9 ∧
        ((nonleaves J).card=10 ∨ FiveOrSixPendant J) := by
  obtain ⟨J,dec,sub,sup,sc,tp,jbad,nine,rest⟩ := residual_eleven_ten_or_four_to_six_tags G t bad
  letI := dec
  have tj : (types J).card=11 := by rwa [tp]
  refine ⟨J,dec,sub,sup,sc,tp,jbad,nine,?_⟩
  rcases rest with q|⟨q,e,f,a,ef,ah,low,en,fn,dense,zmin,zmax,cross⟩
  · exact Or.inl q
  rcases split_profile J sup tj jbad with ⟨qq,_⟩|⟨_,scores,mins,_⟩
  · omega
  · refine Or.inr ⟨q,e,f,a,ef,ah,low,en,fn,dense,?_,zmax,cross⟩
    by_contra! small
    exact (not_le_of_gt jbad) (exact_pendant_four_tags J sup tj nine ah low en fn scores mins dense (by omega))

#print axioms exact_pendant_four_tags
#print axioms residual_eleven_ten_or_five_six_tags
end Graffiti384b.DiversityEleven
