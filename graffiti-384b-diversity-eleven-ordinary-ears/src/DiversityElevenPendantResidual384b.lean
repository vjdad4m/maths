import DiversityElevenOrdinaryEars384b

namespace Graffiti384b.DiversityEleven
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

/-- In the surviving order-eleven branch both low vertices form one pendant
triangle with a high anchor; these are their complete neighbor sets. -/
theorem eleven_pendant_profile (sup : Supported G) (t : (types G).card=11)
    (nine : (high G).card=9) (q : (nonleaves G).card=11) (bad : bound G<gamma G) :
    ∃ e f a, e≠f ∧ a∈high G ∧ nonleaves G \ high G={e,f} ∧
      G.neighborFinset e={f,a} ∧ G.neighborFinset f={e,a} := by
  classical
  have adj : ∃ e∈nonleaves G \ high G, ∃ f∈nonleaves G \ high G, G.Adj e f := by
    by_contra! ind
    exact (not_le_of_gt bad) (exact_eleven_ordinary_ears G sup t nine q ind)
  obtain ⟨e,el,f,fl,ef⟩ := adj
  obtain ⟨x,y,hxy,old⟩ := eleven_two_lows G nine q
  have low : nonleaves G \ high G={e,f} := by
    symm
    apply eq_of_subset_of_card_le _ (by rw [old, card_pair hxy, card_pair ef.ne])
    intro z zm
    simp only [mem_insert,mem_singleton] at zm
    rcases zm with rfl|rfl
    · exact el
    · exact fl
  obtain ⟨a,ea,fa⟩ := sup ef
  have pair {x y : V} (xl : x∈nonleaves G \ high G) (xy : G.Adj x y) (xa : G.Adj x a)
      (ya : y≠a) : G.neighborFinset x={y,a} := by
    symm
    apply eq_of_subset_of_card_le
    · intro z zm
      simp only [mem_insert,mem_singleton] at zm
      rcases zm with rfl|rfl
      · exact (G.mem_neighborFinset ..).mpr xy
      · exact (G.mem_neighborFinset ..).mpr xa
    · rw [card_neighborFinset_eq_degree,card_pair ya]
      have up : ¬3≤G.degree x := fun h => (mem_sdiff.mp xl).2 (mem_filter.mpr ⟨mem_univ _,h⟩)
      omega
  have ah : a∈high G := by
    have ins : ({e,f}:Finset V) ⊆ G.neighborFinset a := by
      intro v vm
      simp only [mem_insert,mem_singleton] at vm
      rcases vm with rfl|rfl
      · exact (G.mem_neighborFinset ..).mpr ea.symm
      · exact (G.mem_neighborFinset ..).mpr fa.symm
    have d := card_le_card ins
    rw [card_pair ef.ne,card_neighborFinset_eq_degree] at d
    by_cases out : a∈high G
    · exact out
    exfalso
    have al : a∈nonleaves G \ high G := mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_univ a,d⟩,out⟩
    rw [low,mem_insert,mem_singleton] at al
    exact al.elim ea.ne.symm fa.ne.symm
  exact ⟨e,f,a,ef.ne,ah,low,pair el ef ea fa.ne,pair fl ef.symm fa ea.ne⟩

theorem residual_eleven_ten_or_pendant (t : (types G).card=11) (bad : bound G<gamma G) :
    ∃ (J : SimpleGraph V) (dec : DecidableRel J.Adj),
      letI := dec
      J ≤ G ∧ Supported J ∧ (∀ v,trianglesAt J v=trianglesAt G v) ∧
        types J=types G ∧ bound J<gamma J ∧ (high J).card=9 ∧
        ((nonleaves J).card=10 ∨
          ((nonleaves J).card=11 ∧ ∃ e f a, e≠f ∧ a∈high J ∧
            nonleaves J \ high J={e,f} ∧
            J.neighborFinset e={f,a} ∧ J.neighborFinset f={e,a})) := by
  obtain ⟨J,dec,sub,sup,sc,tp,jbad,nine,mn,mx⟩ := residual_eleven_orders_ten_eleven G t bad
  letI := dec
  refine ⟨J,dec,sub,sup,sc,tp,jbad,nine,?_⟩
  by_cases q : (nonleaves J).card=10
  · exact Or.inl q
  · have q' : (nonleaves J).card=11 := by omega
    exact Or.inr ⟨q',eleven_pendant_profile J sup (by rwa [tp]) nine q' jbad⟩

#print axioms eleven_pendant_profile
#print axioms residual_eleven_ten_or_pendant
end Graffiti384b.DiversityEleven
