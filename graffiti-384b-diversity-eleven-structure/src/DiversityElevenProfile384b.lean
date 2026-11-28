import DiversityElevenCore384b

namespace Graffiti384b.DiversityEleven
open Finset SimpleGraph
open private TrianglePrune.triangle_iff from TrianglePrune384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem positive_of_nonleaf (sup : Supported G) {v : V} (vm : v∈nonleaves G) :
    0<trianglesAt G v := by
  have dg : 2≤G.degree v := (mem_filter.mp vm).2
  obtain ⟨w,wm⟩ := card_pos.mp (show 0<(G.neighborFinset v).card by
    rw [card_neighborFinset_eq_degree]; omega)
  have vw := (G.mem_neighborFinset _ _).mp wm
  obtain ⟨z,vz,wz⟩ := sup vw
  exact (TrianglePrune.triangle_iff G v).mpr ⟨w,z,vw,vz,wz⟩

/-- In a failing supported graph, either there are exactly ten nonisolated
vertices, all high, or the high set has exactly nine distinct positive
scores greater than one, with every other nonisolated vertex an ear. -/
theorem split_profile (sup : Supported G) (t : (types G).card=11) (bad : bound G<gamma G) :
    ((nonleaves G).card=10 ∧ nonleaves G=high G) ∨
    ((high G).card=9 ∧ Set.InjOn (trianglesAt G) (high G : Set V) ∧
      (∀ v∈high G, 2≤trianglesAt G v) ∧
      ∀ v∈nonleaves G \ high G, G.degree v=2 ∧ 0<trianglesAt G v) := by
  have inc : high G ⊆ nonleaves G := by
    intro v hv
    have h := (mem_filter.mp hv).2
    exact mem_filter.mpr ⟨mem_univ _,by omega⟩
  by_cases eq : nonleaves G=high G
  · have low := (ten_to_fifteen G t bad).1
    have top := (high_profile G t bad).2
    exact Or.inl ⟨by rw [eq] at low ⊢; omega,eq⟩
  · have de {v : V} (vm : v∈nonleaves G \ high G) : G.degree v=2 := by
      have low := (mem_filter.mp (mem_sdiff.mp vm).1).2
      have top : ¬3≤G.degree v := fun a=>(mem_sdiff.mp vm).2
        (mem_filter.mpr ⟨mem_univ _,a⟩)
      omega
    obtain ⟨v,vm⟩ := Finset.nonempty_iff_ne_empty.mpr
      (fun zz => eq (Finset.Subset.antisymm (sdiff_eq_empty_iff_subset.mp zz) inc))
    have pos := positive_of_nonleaf G sup (mem_sdiff.mp vm).1
    obtain ⟨a,b,er,_,_,ab⟩ := PositivePalette.Prerequisites.ear_pair G (de vm) pos
    obtain ⟨c,s,r⟩ := ear_profile G sup t bad er ab
    exact Or.inr ⟨c,s,r,fun _ hm=>⟨de hm,positive_of_nonleaf G sup (mem_sdiff.mp hm).1⟩⟩

/-- Any 2-supported pin block with two or more low-side vertices rules
out a diversity-eleven counterexample. This includes cycles of ears
on high anchors, using all anchors on one side and all ears on the other. -/
theorem exact_of_low_pin_block (t : (types G).card=11)
    {P Q : Finset V} (dis : Disjoint P Q) (low : Disjoint (high G) Q) (two : 2≤Q.card)
    (left : ∀ v∈P, 2≤nbr G v Q) (right : ∀ v∈Q, 2≤nbr G v P) : gamma G≤bound G := by
  by_contra! bad
  have hc := (high_profile G t bad).1
  have win := pinned_budget G dis left right
  have sub : (high G)∪Q ⊆ (high G)∪P∪Q := by
    intro x hx
    rcases mem_union.mp hx with h|h
    · exact mem_union_left _ (mem_union_left _ h)
    · exact mem_union_right _ h
  have c := card_le_card sub
  rw [card_union_of_disjoint low] at c
  unfold bound at bad
  omega

#print axioms split_profile
#print axioms exact_of_low_pin_block
end Graffiti384b.DiversityEleven
