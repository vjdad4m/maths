import PalettePrerequisites

namespace Graffiti384b.PositivePalette
open Finset SimpleGraph
open private Repair.nbr_mono Repair.omit_set Repair.full_nbr from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Both sides give each vertex of W at least two neighbors across the cut. -/
def Covered (W : Finset V) : Prop :=
  ∃ A : Finset V, (∀ v∈W,v∈A → 2≤nbr G v Aᶜ) ∧ (∀ v∈W,v∈Aᶜ → 2≤nbr G v A)

theorem count_covered {W : Finset V} (good : Covered G W) :
    2*gamma G+W.card≤2*Fintype.card V := by
  obtain ⟨A,left,right⟩ := good
  have first := Repair.omit_set G (W∩A) (fun v vm =>
    (left v (mem_inter.mp vm).1 (mem_inter.mp vm).2).trans (Repair.nbr_mono G _ (fun _ h =>
      mem_compl.mpr (fun m => mem_compl.mp h (mem_inter.mp m).2))))
  have second := Repair.omit_set G (W\A) (fun v vm =>
    (right v (mem_sdiff.mp vm).1 (mem_compl.mpr (mem_sdiff.mp vm).2)).trans (Repair.nbr_mono G _ (fun _ h =>
      mem_compl.mpr (fun m => (mem_sdiff.mp m).2 h))))
  have := card_le_univ (W∩A)
  have := card_le_univ (W\A)
  have sizes := card_sdiff_add_card_inter W A
  omega

theorem complete {W P Q : Finset V} (dis : Disjoint P Q)
    (degrees : ∀ v∈W,v∉P → v∉Q → 3≤G.degree v)
    (lp : ∀ v∈P,2≤nbr G v Q) (rq : ∀ v∈Q,2≤nbr G v P) : Covered G W := by
  obtain ⟨A,pa,qb,la,rb⟩ := PinnedColor34.cut G P Q dis
  refine ⟨A,?_,?_⟩
  · intro v vn va
    by_cases vp : v∈P
    · exact (lp v vp).trans (Repair.nbr_mono G v qb)
    · have dg := degrees v vn vp (fun h => mem_compl.mp (qb h) va)
      have ae := la v va vp
      have su := Repair.full_nbr G v A
      omega
  · intro v vn vb
    by_cases vq : v∈Q
    · exact (rq v vq).trans (Repair.nbr_mono G v pa)
    · have dg := degrees v vn (fun h => mem_compl.mp vb (pa h)) vq
      have ae := rb v vb vq
      have su := Repair.full_nbr G v A
      omega

end Graffiti384b.PositivePalette
#print axioms Graffiti384b.PositivePalette.count_covered
#print axioms Graffiti384b.PositivePalette.complete
