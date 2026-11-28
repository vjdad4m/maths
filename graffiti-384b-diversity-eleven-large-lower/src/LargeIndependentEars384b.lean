import FiveOrdinaryEars384b

namespace Graffiti384b.DiversityEleven
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- All lower diversity-eleven skeletons with independent low vertices
and at least fourteen nonisolated vertices satisfy the conjecture. -/
theorem exact_at_least_fourteen_of_independent_ears
    (sup : Supported G) (t : (types G).card=11) (nine : (high G).card=9)
    (large : 14≤(nonleaves G).card)
    (ind : ∀ x∈nonleaves G \ high G,∀ y∈nonleaves G \ high G,¬G.Adj x y) :
    gamma G≤bound G := by
  classical
  by_contra! bad
  let O := nonleaves G \ high G
  have low : Disjoint O (high G) :=
    Finset.disjoint_left.mpr (fun _ xo xh => (mem_sdiff.mp xo).2 xh)
  have sub : high G ⊆ nonleaves G := by
    intro x xh
    have dg := (mem_filter.mp xh).2
    exact mem_filter.mpr ⟨mem_univ _,by omega⟩
  have five : O.card=5 := by
    have c := card_sdiff_add_card_eq_card sub
    have cap := at_most_five_independent_low G t nine bad ind
    dsimp [O]
    omega
  have deg (e : V) (em : e∈O) : G.degree e=2 := by
    obtain ⟨en,eh⟩ := mem_sdiff.mp em
    have up : ¬3≤G.degree e := fun d => eh (mem_filter.mpr ⟨mem_univ _,d⟩)
    have dn := (mem_filter.mp en).2
    omega
  have anchors (e : V) (em : e∈O) (y : V) (ey : G.Adj e y) : y∈high G := by
    obtain ⟨z,ez,yz⟩ := sup ey
    have pair : ({e,z} : Finset V) ⊆ G.neighborFinset y := insert_subset
      ((G.mem_neighborFinset ..).mpr ey.symm)
      (singleton_subset_iff.mpr ((G.mem_neighborFinset ..).mpr yz))
    have d := card_le_card pair
    rw [card_pair ez.ne,card_neighborFinset_eq_degree] at d
    have yn : y∈nonleaves G := mem_filter.mpr ⟨mem_univ _,d⟩
    by_contra yh
    exact ind e em y (mem_sdiff.mpr ⟨yn,yh⟩) ey
  exact (not_le_of_gt bad) (exact_of_five_ordinary_ears G t nine five low deg anchors)

#print axioms exact_at_least_fourteen_of_independent_ears
end Graffiti384b.DiversityEleven
