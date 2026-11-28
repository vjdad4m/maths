import SixSingletonFivePairTail189
import SixSingletonFiveTwoActual189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix.SingletonFive16
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private finish_either sparse_chain route_core_no_strict_hits from SixSingletonFivePairDispatch189
variable {G : SimpleGraph V} [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

/-- All normalized five-visible boards with two balanced dark vertices and six
strict dark vertices are traceable, without an induced dark-degree premise. -/
theorem traceable_of_two_balanced_no_deep {L R S : Finset V}
    (F : ProfileTwo G L R S) (hc : G.Connected) (even : ∀ z,(EvenFrom G z).card≤7) :
    ∃ u v,∃ p : G.Walk u v,p.IsPath ∧ ∀ u,u∈p.support := by
  classical
  have noBoth := two_balanced_no_double_port F hc even
  obtain ⟨z,w,zw,eq⟩ := card_eq_two.mp F.balance
  have zm : z∈D\S := by simp [eq]
  have wm : w∈D\S := by simp [eq]
  have high (t : V) (tm : t∈D) (tz : t≠z) (tw : t≠w) : 4≤(inside G D t).card := by
    have ts : t∈S := by
      by_contra h
      have m := mem_sdiff.mpr ⟨tm,h⟩
      rw [eq,mem_insert,mem_singleton] at m
      exact m.elim tz tw
    exact (by decide : 4≤5).trans (F.dark5 t ts)
  have mixed {i j : V} (im : i∈D\S) (jm : j∈D\S) (ij : i≠j)
      (low : (inside G D i).card≤3) (hj : 4≤(inside G D j).card) :
      ∃ u v,∃ p : G.Walk u v,p.IsPath ∧ ∀ u,u∈p.support := by
    obtain ⟨l,lm,p⟩ := dark_route_with_one_low F im jm ij hj
    obtain ⟨c,_,t,tm,q,edge⟩ := early_common_plan F im jm ij low noBoth
    exact finish_either F (mem_union_left _ lm) p q edge tm
  by_cases hz : 4≤(inside G D z).card
  · by_cases hw : 4≤(inside G D w).card
    · apply traceable_of_two_balanced_dark_dense F hc even
      intro t tm
      by_cases h : t=z
      · exact h.symm ▸ hz
      by_cases j : t=w
      · exact j.symm ▸ hw
      exact high t tm h j
    exact mixed wm zm zw.symm (by omega) hz
  by_cases hw : 4≤(inside G D w).card
  · exact mixed zm wm zw (by omega) hw
  have zl : (inside G D z).card≤3 := by omega
  have wl : (inside G D w).card≤3 := by omega
  by_cases zw' : G.Adj z w
  · by_cases zHit : ∃ t∈S,G.Adj t z
    · obtain ⟨t,tm,tz⟩ := zHit
      exact sparse_chain F zm wm zw' tm tz wl noBoth
    by_cases wHit : ∃ t∈S,G.Adj t w
    · obtain ⟨t,tm,tw⟩ := wHit
      exact sparse_chain F wm zm zw'.symm tm tw zl noBoth
    exact route_core_no_strict_hits F zm wm zw' zHit wHit wl noBoth
  exact traceable_nonadjacent_two_low F zm wm zw zw' zl wl noBoth

#print axioms traceable_of_two_balanced_no_deep
end Graffiti189LongestPath.CrossSaturation.ThresholdSix.SingletonFive16
