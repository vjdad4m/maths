import SixSingletonQ1Slots189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph Finset ArticulationPair PortCertificates
open private Cmp from SixCutFar189
open private Vis from AdjacentCutFiveComponents189
open private Dark Common strictA strictB from SixSingletonGeometry189
open private nearBal from SixSingletonFiveGeometry189
open private EA EB from SixSingletonMultiZeroGeom189
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {a b s z : V} {D : Cmp G a b}
set_option linter.unusedSectionVars false

theorem q1_dark_parts_subsets (F : SixVisibleData G D s) :
    strictA D⊆Dark D ∧ strictB D⊆Dark D ∧ nearBal D⊆Dark D := by
  rw [←F.darkPart]
  exact ⟨subset_union_left.trans subset_union_left,subset_union_right.trans subset_union_left,subset_union_right⟩

theorem q1_inactive_left (F : SixVisibleData G D s) (bal : nearBal D={z})
    {J : Finset V} (Jmax : (Dark D).erase z⊆J) {x : V} (hx : x∈EA D)
    (off : ¬∃ w∈J,G.Adj x w) :
    5 ≤ (inside G (Vis D) x).card+marks (decide (G.Adj x z)) := by
  have h := card_le_card (F.aBound x hx)
  have k : (inside G (nearBal D) x).card = marks (decide (G.Adj x z)) := by
    rw [bal]; by_cases e : G.Adj x z <;> simp [inside,Finset.filter_singleton,e,marks]
  have empty : inside G (strictA D) x = ∅ := by
    apply eq_empty_iff_forall_not_mem.mpr
    intro w hw
    obtain ⟨wl,xw⟩ := mem_filter.mp hw
    have dark := (q1_dark_parts_subsets F).1 wl
    have ne : w≠z := by
      intro e
      subst w
      have v := (mem_filter.mp wl).2
      have wt : z∈nearBal D := by rw [bal]; simp
      have rr := (mem_filter.mp (mem_filter.mp wt).1).2
      omega
    exact off ⟨w,Jmax (mem_erase.mpr ⟨ne,dark⟩),xw⟩
  rw [empty,union_empty,card_neighborFinset_eq_degree] at h
  have h' := card_insert_le a (inside G (Vis D) x ∪ inside G (nearBal D) x)
  have i := card_union_le (inside G (Vis D) x) (inside G (nearBal D) x)
  have g := F.highEA x hx
  omega

theorem q1_inactive_right (F : SixVisibleData G D s) (bal : nearBal D={z})
    {J : Finset V} (Jmax : (Dark D).erase z⊆J) {x : V} (hx : x∈EB D)
    (off : ¬∃ w∈J,G.Adj x w) :
    5 ≤ (inside G (Vis D) x).card+marks (decide (G.Adj x z)) := by
  have h := card_le_card (F.bBound x hx)
  have k : (inside G (nearBal D) x).card = marks (decide (G.Adj x z)) := by
    rw [bal]; by_cases e : G.Adj x z <;> simp [inside,Finset.filter_singleton,e,marks]
  have empty : inside G (strictB D) x = ∅ := by
    apply eq_empty_iff_forall_not_mem.mpr
    intro w hw
    obtain ⟨wr,xw⟩ := mem_filter.mp hw
    have dark := (q1_dark_parts_subsets F).2.1 wr
    have ne : w≠z := by
      intro e
      subst w
      have v := (mem_filter.mp wr).2
      have wt : z∈nearBal D := by rw [bal]; simp
      have rr := (mem_filter.mp (mem_filter.mp wt).1).2
      omega
    exact off ⟨w,Jmax (mem_erase.mpr ⟨ne,dark⟩),xw⟩
  rw [empty,union_empty,card_neighborFinset_eq_degree] at h
  have h' := card_insert_le b (inside G (Vis D) x ∪ inside G (nearBal D) x)
  have i := card_union_le (inside G (Vis D) x) (inside G (nearBal D) x)
  have g := F.highEB x hx
  omega

#print axioms q1_inactive_left
#print axioms q1_inactive_right
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
