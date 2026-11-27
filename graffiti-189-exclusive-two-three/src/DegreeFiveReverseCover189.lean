import DegreeFiveActualCut189
import DegreeFiveDistanceTwoThreeClose189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph Finset
open private CutGraph Shore shore_off shore_closed shore_disjoint from DegreeFiveActualCut189
open private secondShore from DegreeFiveDistanceTwoThreeClose189
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

/-- All opposite nonports lie within two of at least one cut vertex
when five opposite ports saturate a common vertex's even budget. -/
theorem exclusive_nonports_in_cut_shells_at_five
    (hc : G.Connected)
    (even : ∀ x, (EvenFrom G x).card ≤ 6)
    {C D : (CutGraph (G:=G) a b).ConnectedComponent} (cd : C ≠ D)
    {x : V} (xc : x ∈ Shore C) (ax : G.Adj a x) (bx : G.Adj b x)
    (five : (cutPorts D).card = 5) :
    Shore D ⊆ cutPorts D ∪ (secondShore D a ∪ secondShore D b) := by
  classical
  have foreign : cutPorts D ⊆ DistanceTwo G x := by
    intro w hw
    obtain ⟨wd,ha|hb⟩ := mem_filter.mp hw
    all_goals
      have wc : w ∉ Shore C := fun h => disjoint_left.mp (shore_disjoint cd) h wd
      have ne : x ≠ w := fun e => wc (Eq.mp (congrArg (fun v : V => v ∈ Shore C) e) xc)
      have no : ¬ G.Adj x w := fun h => by
        rcases shore_closed C x xc w h with rfl|rfl|h
        · exact (shore_off D).1 wd
        · exact (shore_off D).2 wd
        · exact wc h
    · exact d2 hc ne no ax.symm ha
    · exact d2 hc ne no bx.symm hb
  have dlow := card_le_card foreign
  have near (w : V) : G.dist x w ≤ 3 := by
    by_contra! hfar
    have big := distanceTwo_add_two_le_even_of_far hc (show 4 ≤ G.dist x w by omega)
    have bound := even x
    omega
  intro w wd
  by_cases h : G.Adj a w ∨ G.Adj b w
  · exact mem_union_left _ (mem_filter.mpr ⟨wd,h⟩)
  have xa : G.dist x a = 1 := dist_eq_one_iff_adj.mpr ax.symm
  have xb : G.dist x b = 1 := dist_eq_one_iff_adj.mpr bx.symm
  have wc : w ∉ Shore C := fun h => disjoint_left.mp (shore_disjoint cd) h wd
  have eq := cross_metric (Shore C) hc xc wc (shore_closed C)
  rw [xa, xb] at eq
  have ja : a ≠ w := fun e => (shore_off D).1 (Eq.mp (congrArg (fun v : V => v ∈ Shore D) e.symm) wd)
  have jb : b ≠ w := fun e => (shore_off D).2 (Eq.mp (congrArg (fun v : V => v ∈ Shore D) e.symm) wd)
  have na : ¬ G.Adj a w := fun e => h (.inl e)
  have nb : ¬ G.Adj b w := fun e => h (.inr e)
  have la := hc.one_lt_dist_of_ne_of_not_adj ja na
  have lb := hc.one_lt_dist_of_ne_of_not_adj jb nb
  have small := near w
  apply mem_union_right
  by_cases da : G.dist a w = 2
  · exact mem_union_left _ (mem_inter.mpr ⟨wd,by simpa [DistanceTwo] using da⟩)
  · have db : G.dist b w = 2 := by omega
    exact mem_union_right _ (mem_inter.mpr ⟨wd,by simpa [DistanceTwo] using db⟩)

#print axioms exclusive_nonports_in_cut_shells_at_five
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
