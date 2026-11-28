import SixSingletonFiveThreeActualTwoTiny189
import SixSingletonFiveThreeActualTwoLowMix189
import SixSingletonFiveResidualSmall189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private Shore from AdjacentCutFiveActual189
open private Cmp DeletionConnected from SixCutFar189
open private Vis from AdjacentCutFiveComponents189
open private Dark from SixSingletonGeometry189
open private nearBal from SixSingletonFiveGeometry189
open private m5_dark_nonbalance_high from SixSingletonFiveResidualTwoLow189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

/-- The five-visible three-balance case is traceable if any balance has
dark degree at least four, with no condition on the other two. -/
theorem traceable_of_adjacent_singleton_thirteen_five_three_balanced_has_high
    (hc : G.Connected) (ab : G.Adj a b)
    (even : ∀ z,(EvenFrom G z).card≤7) (conn : DeletionConnected G)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {S D : Cmp G a b} (sd : S≠D)
    (cover : ∀ {z : V},z≠a → z≠b → z∈Shore S ∨ z∈Shore D)
    (one : (Shore S).card=1) (d13 : (Shore D).card=13)
    (v5 : (Vis D).card=5) (q3 : (nearBal D).card=3)
    {h : V} (hh : h∈nearBal D) (h4 : 4≤(inside G (Dark D) h).card) :
    ∃ u v,∃ p : G.Walk u v,p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  by_cases min3 : ∀ z∈Dark D,3≤(inside G (Dark D) z).card
  · exact traceable_of_adjacent_singleton_thirteen_five_three_balanced_dark_min_three hc ab even conn degree
      sd cover one d13 v5 q3 min3
  push_neg at min3
  obtain ⟨z,zd,zl⟩ := min3
  have zb : z∈nearBal D := by
    by_contra not
    have p := m5_dark_nonbalance_high hc ab even conn degree sd cover one d13 v5 z zd not
    omega
  have zh : z≠h := by intro e; subst h; omega
  have slot : ∃ w∈nearBal D,w≠z ∧ w≠h := by
    by_contra no
    have in2 : nearBal D⊆({z,h}:Finset V) := by
      intro w wm
      by_cases wz : w=z
      · exact mem_insert.mpr (.inl wz)
      by_cases wh : w=h
      · exact mem_insert.mpr (.inr (mem_singleton.mpr wh))
      exact (no ⟨w,wm,wz,wh⟩).elim
    have p := card_le_card in2
    rw [q3,card_insert_of_not_mem (by simpa using zh),card_singleton] at p
    omega
  obtain ⟨w,wb,wz,wh⟩ := slot
  by_cases w3 : 3≤(inside G (Dark D) w).card
  · exact traceable_of_adjacent_singleton_thirteen_five_three_balanced_two_low_mix hc ab even conn degree
      sd cover one d13 v5 q3 zb wb hh wz.symm zh wh (by omega) w3 h4
  exact traceable_of_adjacent_singleton_thirteen_five_three_balanced_two_tiny hc ab even conn degree
    sd cover one d13 v5 q3 zb wb hh wz.symm zh wh (by omega) (by omega) h4

#print axioms traceable_of_adjacent_singleton_thirteen_five_three_balanced_has_high
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
