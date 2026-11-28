import SixSingletonMultiTransport189
import SixSingletonAdjacentUniqueComplete189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private Shore from AdjacentCutFiveActual189
open private Cmp aPorts bPorts DeletionConnected from SixCutFar189
open private Vis from AdjacentCutFiveComponents189
open private Dark strictA strictB bal from SixSingletonGeometry189
open private nearBal from SixSingletonFiveGeometry189
open private EA EB from SixSingletonMultiZeroGeom189
open private board22_of_data board12_of_data both_strict_nonempty from SixSingletonMultiTransport189
open private shore_sum_with_cover from AdjacentCutFiveMixedFourteenSixteen189
open private swapCut from AdjacentCutFiveMixedNineGeom189
open FiveAdjacent (shore_swapCut depth)
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

private theorem mixed_zero_oriented
    (hc : G.Connected) (ab : G.Adj a b)
    (even : ∀ z,(EvenFrom G z).card≤7) (conn : DeletionConnected G)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {S D : Cmp G a b} (sd : S≠D)
    (cover : ∀ {z : V},z≠a → z≠b → z∈Shore S ∨ z∈Shore D)
    (one : (Shore S).card=1) (d13 : (Shore D).card=13)
    (v6 : (Vis D).card=6) (zero : (nearBal D).card=0)
    (ea : (EA D).card=1 ∨ (EA D).card=2) (eb : (EB D).card=2) :
    ∃ u v,∃ p : G.Walk u v,p.IsPath ∧ ∀ z,z∈p.support := by
  obtain ⟨s,F⟩ := isolate_zero_balance_geometry hc ab even conn degree sd cover one d13 v6 zero
  have size : Fintype.card V=16 := by
    have k := shore_sum_with_cover ab.ne sd cover
    omega
  have near : ∀ z∈Dark D,depth G a b z=2 := by
    rcases adjacent_singleton_thirteen_visible_profile hc ab even conn degree sd cover one d13 with
       ⟨n,_,_,_⟩|⟨_,_,_,_,_,j⟩
    · omega
    exact j
  obtain ⟨L,R⟩ := both_strict_nonempty even F near
  rcases ea with h|h
  · exact board12_of_data F size v6 h eb L R
  exact board22_of_data F size v6 h eb L R

/-- For degree six, an adjacent separator leaving a singleton plus thirteen has
a spanning path if there are six visible ports and no balanced dark vertex. -/
theorem traceable_of_adjacent_singleton_thirteen_six_zero_balance
    (hc : G.Connected) (ab : G.Adj a b)
    (even : ∀ z,(EvenFrom G z).card≤7) (conn : DeletionConnected G)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {S D : Cmp G a b} (sd : S≠D)
    (cover : ∀ {z : V},z≠a → z≠b → z∈Shore S ∨ z∈Shore D)
    (one : (Shore S).card=1) (d13 : (Shore D).card=13)
    (v6 : (Vis D).card=6) (zero : (nearBal D).card=0) :
    ∃ u v,∃ p : G.Walk u v,p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  have ⟨la,ua,lb,ub⟩ : 1≤(EA D).card ∧ (EA D).card≤2 ∧ 1≤(EB D).card ∧ (EB D).card≤2 := by
    rcases adjacent_singleton_thirteen_visible_profile hc ab even conn degree sd cover one d13 with
       ⟨n,_,_,_⟩|⟨_,p,q,r,t,_⟩
    · omega
    exact ⟨p,q,r,t⟩
  have ea : (EA D).card=1 ∨ (EA D).card=2 := by omega
  by_cases hB : (EB D).card=2
  · exact mixed_zero_oriented hc ab even conn degree sd cover one d13 v6 zero ea hB
  have b1 : (EB D).card=1 := by omega
  rcases ea with a1|a2
  · exact traceable_of_adjacent_singleton_thirteen_unique hc ab even conn degree sd cover one d13 v6 a1 b1
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
  have aSwap : EA (swapCut D)=EB D := by unfold EA EB aPorts bPorts; rw [shD]
  have bSwap : EB (swapCut D)=EA D := by unfold EA EB aPorts bPorts; rw [shD]
  exact mixed_zero_oriented hc ab.symm even conn degree
    (fun h=>sd (swapCut.injective h)) (fun zb za=>by rw [shS,shD]; exact cover za zb)
    (shS.symm ▸ one) (shD.symm ▸ d13) (vSwap.symm ▸ v6) (qSwap.symm ▸ zero)
    (.inl (aSwap.symm ▸ b1)) (bSwap.symm ▸ a2)

#print axioms traceable_of_adjacent_singleton_thirteen_six_zero_balance
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
