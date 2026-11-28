import SixSingletonQ1Complete189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph Finset ArticulationPair Graffiti189Ore
open private Shore from AdjacentCutFiveActual189
open private Cmp aPorts bPorts DeletionConnected from SixCutFar189
open private Vis from AdjacentCutFiveComponents189
open private Dark bal from SixSingletonGeometry189
open private nearBal from SixSingletonFiveGeometry189
open private EA EB from SixSingletonMultiZeroGeom189
open private shore_sum_with_cover from AdjacentCutFiveMixedFourteenSixteen189
open private swapCut from AdjacentCutFiveMixedNineGeom189
open FiveAdjacent (shore_swapCut depth)
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

/-- An adjacent cut leaving a singleton and a thirteen-vertex shore is traceable
at degree six with six visible ports and exactly one balanced dark vertex. -/
theorem traceable_of_adjacent_singleton_thirteen_six_one_balance
    (hc : G.Connected) (ab : G.Adj a b)
    (even : ∀ z,(EvenFrom G z).card≤7) (conn : DeletionConnected G)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {S D : Cmp G a b} (sd : S≠D)
    (cover : ∀ {z : V},z≠a → z≠b → z∈Shore S ∨ z∈Shore D)
    (one : (Shore S).card=1) (d13 : (Shore D).card=13)
    (v6 : (Vis D).card=6) (q1 : (nearBal D).card=1) : Traceable G := by
  classical
  have n : Fintype.card V=16 := by
    have k := shore_sum_with_cover ab.ne sd cover
    omega
  have ⟨la,ua,lb,ub⟩ : 1≤(EA D).card ∧ (EA D).card≤2 ∧ 1≤(EB D).card ∧ (EB D).card≤2 := by
    rcases adjacent_singleton_thirteen_visible_profile hc ab even conn degree sd cover one d13 with
       ⟨m,_,_,_⟩|⟨_,p,q,r,t,_⟩
    · omega
    exact ⟨p,q,r,t⟩
  by_cases b2 : (EB D).card=2
  · exact traceable_at_adjacent_singleton_thirteen_six_visible_one_balance_right_two
      hc ab even conn degree n sd cover one d13 v6 b2 q1
  have b1 : (EB D).card=1 := by omega
  by_cases a1 : (EA D).card=1
  · exact traceable_of_adjacent_singleton_thirteen_unique hc ab even conn degree sd cover one d13 v6 a1 b1
  have a2 : (EA D).card=2 := by omega
  have shS := shore_swapCut S
  have shD := shore_swapCut D
  have vSwap : Vis (swapCut D)=Vis D := by
    unfold Vis
    rw [shD]
    ext z
    simp [or_comm]
  have dSwap : Dark (swapCut D)=Dark D := by unfold Dark; rw [shD,vSwap]
  have qSwap : nearBal (swapCut D)=nearBal D := by
    unfold nearBal bal
    rw [dSwap]
    ext z
    simp [depth,min_comm,eq_comm]
  have bSwap : EB (swapCut D)=EA D := by unfold EA EB aPorts bPorts; rw [shD]
  exact traceable_at_adjacent_singleton_thirteen_six_visible_one_balance_right_two hc ab.symm even conn degree n
    (fun h=>sd (swapCut.injective h)) (fun zb za=>by rw [shS,shD]; exact cover za zb)
    (shS.symm ▸ one) (shD.symm ▸ d13) (vSwap.symm ▸ v6) (bSwap.symm ▸ a2) (qSwap.symm ▸ q1)

#print axioms traceable_of_adjacent_singleton_thirteen_six_one_balance
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
