import HighEarScoreDecomp384b

namespace Graffiti384b.DiversityEleven
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Extend the retained high set by retaining exactly the low vertices
that cannot already be 2-dominated by it. -/
def retainedFromHigh (H S : Finset V) : Finset V :=
  S ∪ (Hᶜ.filter (fun x => ¬ (2 ≤ G.degree x ∧ G.neighborFinset x ⊆ S)))

theorem retainedFromHigh_normalizes {H D : Finset V}
    (small : ∀ x∉H, G.degree x≤2)
    (indep : ∀ x∉H, ∀ y∉H, ¬G.Adj x y)
    (td : TwoDominates G D) :
    retainedFromHigh G H (D∩H) ⊆ D ∧
      TwoDominates G (retainedFromHigh G H (D∩H)) := by
  classical
  let S := D∩H
  let R := retainedFromHigh G H S
  have keep : S ⊆ R := subset_union_left
  have typ {x : V} (h : x ∉ H) (xe : x∉D) :
      2≤G.degree x ∧ G.neighborFinset x⊆S := by
    have dm := td x xe
    have ns : D.filter (G.Adj x)⊆G.neighborFinset x := fun z zm =>
      (G.mem_neighborFinset ..).mpr (mem_filter.mp zm).2
    have eq : D.filter (G.Adj x)=G.neighborFinset x := by
      refine eq_of_subset_of_card_le ns ?_
      rw [card_neighborFinset_eq_degree]
      exact (small x h).trans dm
    constructor
    · rwa [nbr,eq,card_neighborFinset_eq_degree] at dm
    · intro y ym
      have hy : y∈D := (mem_filter.mp (eq ▸ ym)).1
      have yH : y∈H := by
        by_contra nh
        exact indep x h y nh ((G.mem_neighborFinset ..).mp ym)
      exact mem_inter.mpr ⟨hy,yH⟩
  have sub : R⊆D := by
    intro x hx
    rcases mem_union.mp hx with xs|xl
    · exact (mem_inter.mp xs).1
    · obtain ⟨xo,xn⟩ := mem_filter.mp xl
      by_contra xd
      exact xn (typ (mem_compl.mp xo) xd)
  refine ⟨sub,?_⟩
  intro x xr
  by_cases xH : x∈H
  · have xd : x∉D := fun hm => xr (keep (mem_inter.mpr ⟨hm,xH⟩))
    have ss : D.filter (G.Adj x) ⊆ R.filter (G.Adj x) := by
      intro y ym
      obtain ⟨yd,xy⟩ := mem_filter.mp ym
      apply mem_filter.mpr
      refine ⟨?_,xy⟩
      by_contra ry
      have yh : y∉H := fun h => ry (keep (mem_inter.mpr ⟨yd,h⟩))
      have yc : 2≤G.degree y ∧ G.neighborFinset y⊆S := by
        by_contra n
        exact ry (mem_union_right _ (mem_filter.mpr ⟨mem_compl.mpr yh,n⟩))
      exact xr (keep (yc.2 ((G.mem_neighborFinset ..).mpr xy.symm)))
    exact (td x xd).trans (card_le_card ss)
  · have xc : 2≤G.degree x ∧ G.neighborFinset x⊆S := by
      by_contra n
      exact xr (mem_union_right _ (mem_filter.mpr ⟨mem_compl.mpr xH,n⟩))
    have ss : G.neighborFinset x⊆R.filter (G.Adj x) := fun y ym =>
      mem_filter.mpr ⟨keep (xc.2 ym),(G.mem_neighborFinset ..).mp ym⟩
    exact xc.1.trans (by simpa only [card_neighborFinset_eq_degree] using card_le_card ss)

#print axioms retainedFromHigh_normalizes
end Graffiti384b.DiversityEleven
