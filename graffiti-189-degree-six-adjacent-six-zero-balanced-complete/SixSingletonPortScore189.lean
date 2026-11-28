import SixSingletonPortLabel189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph Finset ArticulationPair
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

theorem visible_four_forces_either (P : Finset V) {c x y : V} (p6 : P.card=6)
    (mc : c∈P) (mx : x∈P) (my : y∈P) (cx : c≠x) (cy : c≠y) (xy : x≠y)
    (deg : 4≤(inside G P c).card) : G.Adj c x ∨ G.Adj c y := by
  classical
  by_contra h
  push_neg at h
  have x1 : x∈P.erase c := mem_erase.mpr ⟨Ne.symm cx,mx⟩
  have y1 : y∈(P.erase c).erase x := mem_erase.mpr ⟨Ne.symm xy,mem_erase.mpr ⟨Ne.symm cy,my⟩⟩
  have sub : inside G P c ⊆ ((P.erase c).erase x).erase y := by
    intro z hz
    obtain ⟨m,cz⟩ := mem_filter.mp hz
    have nzx : z≠x := fun e=>h.1 (e ▸ cz)
    have nzy : z≠y := fun e=>h.2 (e ▸ cz)
    exact mem_erase.mpr ⟨nzy,mem_erase.mpr ⟨nzx,mem_erase.mpr ⟨cz.ne.symm,m⟩⟩⟩
  have cap := card_le_card sub
  have i := card_erase_add_one mc
  have j := card_erase_add_one x1
  have k := card_erase_add_one y1
  omega

theorem inside_insert_score {P : Finset V} {x c : V} (notMem : x∉P) :
    (inside G (insert x P) c).card=
      (inside G P c).card + PortCertificates.marks (decide (G.Adj c x)) := by
  by_cases h : G.Adj c x
  · have xno : x∉P.filter (G.Adj c) := fun j=>notMem (mem_filter.mp j).1
    unfold inside
    rw [filter_insert,if_pos h,card_insert_of_not_mem xno]
    simp [PortCertificates.marks,h]
  · unfold inside
    rw [filter_insert,if_neg h]
    simp [PortCertificates.marks,h]

#print axioms visible_four_forces_either
#print axioms inside_insert_score
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
