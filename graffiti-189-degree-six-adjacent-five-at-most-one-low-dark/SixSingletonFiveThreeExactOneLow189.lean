import SixSingletonFiveThreeLowPorts189
import SixEightRemoveOneLow189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix.SingletonFive16
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private d8 p5 finish_by_balance from SixSingletonFiveShallowRoute189
open private dark_core_five from SixSingletonFiveThreeBase189
open private erase_internal_deg from SixSingletonDarkOre189
open FiveAdjacent (terminal_route_on_of_local_ore)
variable {G : SimpleGraph V} [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

theorem three_balances_route_with_exactly_one_low {L R S : Finset V} {T z : V}
    (F : ProfileThree G L R S T) (hc : G.Connected)
    (even : ∀ w,(EvenFrom G w).card≤7)
    (zW : z∈D\S) (low : (inside G D z).card≤3)
    (condition : ∀ w∈D\S,w≠z → 4≤(inside G D w).card) :
    ∃ u v,∃ p : G.Walk u v,p.IsPath ∧ ∀ u,u∈p.support := by
  classical
  obtain ⟨c,cm,t,tm,tail,zc⟩ := three_balance_low_can_exit F hc even zW low
  have zd := (mem_sdiff.mp zW).1
  have zs := (mem_sdiff.mp zW).2
  have left2 : 1<L.card := by rw [F.l2]; decide
  have core5 := dark_core_five F
  have d4 (w : V) (wd : w∈D) (wz : w≠z) : 4≤(inside G D w).card := by
    by_cases ws : w∈S
    · exact (by decide : 4≤5).trans (F.dark5 w ws)
    exact condition w (mem_sdiff.mpr ⟨wd,ws⟩) wz
  have get : ∃ l∈L,RouteOn G D l z := by
    by_cases z3 : 3≤(inside G D z).card
    · obtain ⟨l,lm,lz⟩ := exists_ne_of_one_lt_card left2 z
      exact ⟨l,lm,eight_high_core_weighted_low_route D S F.core_sub d8 (by rw [core5]) F.dark5
        (F.core_sub (F.left_sub lm)) zd lz z3 d4⟩
    have hit : ∃ w∈D,G.Adj w z := by
      by_contra no
      have sub : G.neighborFinset z⊆P := by
        intro w wm
        have e := (mem_neighborFinset _ _ _).mp wm
        exact (mem_union.mp (F.darkBounds z zd w e)).resolve_left (fun m=>no ⟨w,m,e.symm⟩)
      have q := card_le_card sub
      rw [card_neighborFinset_eq_degree,p5] at q
      have k := F.darkHigh z zd
      omega
    exact eight_remove_one_low_route D S L F.left_sub F.core_sub d8 (by rw [core5])
      (by rw [F.l2]) zd zs (by omega) hit F.dark5 d4
  obtain ⟨l,lm,p⟩ := get
  exact finish_by_balance p tail F.sa F.ax (F.xL l lm) zc (F.commonB t tm).symm F.by'

#print axioms three_balances_route_with_exactly_one_low
end Graffiti189LongestPath.CrossSaturation.ThresholdSix.SingletonFive16
