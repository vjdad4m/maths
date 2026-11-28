import UpperClique
namespace Graffiti384b.OddStars.PaletteCorollaries
open Finset SimpleGraph PositivePalette LeafCritical
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The upper skeletal profile of a failure is exactly omission of the score one. -/
theorem upper_iff_no_one (bad : bound G<gamma G) :
    (high (patch G ∅)).card+1=(types G).card ↔ 1∉types G := by
  let J := patch G ∅
  let H := high J
  have hd {v : V} (vm : v∈H) : 2≤trianglesAt G v := by
    have d : 3≤J.degree v := (mem_filter.mp vm).2
    have a := skeleton_degree_bound G v; change J.degree v≤_ at a
    omega
  constructor
  · intro sz one
    obtain ⟨v,_,eq⟩ := mem_image.mp one
    have p := (PendantAudit.upper_branch G bad sz).1 v (by omega)
    have b := hd p; omega
  · intro missing
    have same : H.image (trianglesAt G)=(types G).erase 0 := by
      ext k
      constructor
      · intro km; obtain ⟨v,vm,rfl⟩ := mem_image.mp km
        have lo := hd vm
        exact mem_erase.mpr ⟨by omega,mem_image_of_mem _ (mem_univ v)⟩
      · intro km
        obtain ⟨nz,old⟩ := mem_erase.mp km
        have no : k≠1 := fun eq => missing (eq ▸ old)
        obtain ⟨v,_,rfl⟩ := mem_image.mp old
        exact mem_image.mpr ⟨v,rich_high G (by omega) ∅,rfl⟩
    have inj : Set.InjOn (trianglesAt G) (H : Set V) :=
      fun _ xm _ _ eq => distinct_rich G bad (hd xm) eq
    have card := congrArg Finset.card same
    rw [card_image_iff.mpr inj] at card
    have one := card_erase_add_one ((failure_requires_odd_zero G bad).2)
    change H.card+1=(types G).card
    omega

/-- A five-clique and absence of score one suffice for the catalogue bound at any order. -/
theorem exact_of_five_no_one (one : 1∉types G) {C : Finset V} (five : G.IsNClique 5 C) :
    gamma G≤bound G := by
  apply Nat.le_of_not_gt
  intro bad
  exact UpperClique.no_five G bad ((upper_iff_no_one G bad).mpr one) C five

/-- In the original connected problem, absence of score one forces both
scores two and three in any failure, as well as the fixed skeletal cubics. -/
theorem missing_one_failure (conn : G.Connected) (order : 2<Fintype.card V) (bad : bound G<gamma G)
    (one : 1∉types G) :
    (∀C,¬G.IsNClique 5 C) ∧
    ∃u v : V,u≠v ∧ trianglesAt G u=2 ∧ trianglesAt G v=3 ∧ ¬(patch G ∅).Adj u v ∧
      (∀x,(patch G ∅).degree x=3 ↔ x=u ∨ x=v) ∧
      ∀A : Finset V,Maximum (patch G ∅) A → critical (patch G ∅) A={u,v} := by
  have sz := (upper_iff_no_one G bad).mpr one
  have large : 4<(types G).card := by
    by_contra! small
    exact (not_lt_of_ge (exact_of_at_most_four G conn order small)) bad
  have has : (high (patch G ∅)).Nonempty := card_pos.mp (by omega)
  exact ⟨UpperClique.no_five G bad sz,FixedCubics.fixed_pair G bad sz has⟩

/-- If score one is absent, missing either two or three also suffices. -/
theorem exact_of_two_gaps (conn : G.Connected) (order : 2<Fintype.card V)
    (one : 1∉types G) (gap : 2∉types G ∨ 3∉types G) : gamma G≤bound G := by
  apply Nat.le_of_not_gt
  intro bad
  obtain ⟨_,u,v,_,su,sv,_⟩ := missing_one_failure G conn order bad one
  exact gap.elim (fun no => no (mem_image.mpr ⟨u,mem_univ _,su⟩))
    (fun no => no (mem_image.mpr ⟨v,mem_univ _,sv⟩))
end Graffiti384b.OddStars.PaletteCorollaries
#print axioms Graffiti384b.OddStars.PaletteCorollaries.upper_iff_no_one
#print axioms Graffiti384b.OddStars.PaletteCorollaries.exact_of_five_no_one
#print axioms Graffiti384b.OddStars.PaletteCorollaries.missing_one_failure
#print axioms Graffiti384b.OddStars.PaletteCorollaries.exact_of_two_gaps
