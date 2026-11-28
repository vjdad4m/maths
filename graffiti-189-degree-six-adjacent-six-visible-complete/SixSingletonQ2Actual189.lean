import SixSingletonQ2OriginalData189
import SixSingletonQ2Semantic189
import SixSingletonQ2Reduction189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph Finset ArticulationPair Graffiti189Ore
open private Shore from AdjacentCutFiveActual189
open private Cmp aPorts bPorts DeletionConnected from SixCutFar189
open private Vis from AdjacentCutFiveComponents189
open private Dark strictA strictB bal from SixSingletonGeometry189
open private nearLeft nearRight nearBal from SixSingletonFiveGeometry189
open private EA EB from SixSingletonMultiZeroGeom189
open private shore_sum_with_cover from AdjacentCutFiveMixedFourteenSixteen189
open private swapCut from AdjacentCutFiveMixedNineGeom189
open FiveAdjacent (shore_swapCut depth traceable_label)
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

private theorem two_balance_oriented
    (hc : G.Connected) (ab : G.Adj a b) (even : ∀ z,(EvenFrom G z).card≤7)
    (conn : DeletionConnected G) (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {S D : Cmp G a b} (sd : S≠D)
    (cover : ∀ {z : V},z≠a → z≠b → z∈Shore S ∨ z∈Shore D)
    (one : (Shore S).card=1) (d13 : (Shore D).card=13) (v6 : (Vis D).card=6)
    (q2 : (nearBal D).card=2) (ae : (EA D).card=1) (be : (EB D).card=2)
    (la : (nearLeft D).card=2) (rb : (nearRight D).card=3) : Traceable G := by
  classical
  obtain ⟨s,F⟩ := isolate_six_visible_geometry hc ab even conn degree sd cover one d13 v6
  have n : Fintype.card V=16 := by
    have k := shore_sum_with_cover ab.ne sd cover
    omega
  rw [F.nearA] at la
  rw [F.nearB] at rb
  obtain ⟨P⟩ := Q2.choose_original_label F n v6 ae be la rb q2
  apply traceable_label (SimpleGraph.Iso.comap P.e G)
  exact Q2.traceable_of_data (Q2.data_of_original hc ab even degree F P)

/-- All six-visible branches of the order-sixteen adjacent singleton cut. -/
theorem traceable_of_adjacent_singleton_thirteen_six_visible
    (hc : G.Connected) (ab : G.Adj a b) (even : ∀ z,(EvenFrom G z).card≤7)
    (conn : DeletionConnected G) (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {S D : Cmp G a b} (sd : S≠D)
    (cover : ∀ {z : V},z≠a → z≠b → z∈Shore S ∨ z∈Shore D)
    (one : (Shore S).card=1) (d13 : (Shore D).card=13) (v6 : (Vis D).card=6) : Traceable G := by
  classical
  by_contra bad
  obtain ⟨q2,⟨ae,be,l,r⟩|⟨ae,be,l,r⟩⟩ :=
    adjacent_six_counterexample_exact_two_balance_shape hc ab even conn degree sd cover one d13 v6 bad
  · exact bad (two_balance_oriented hc ab even conn degree sd cover one d13 v6 q2 ae be l r)
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
  have lSwap : nearLeft (swapCut D)=nearRight D := by
    unfold nearLeft nearRight strictA strictB
    rw [dSwap]
    ext z
    simp [depth,min_comm]
  have rSwap : nearRight (swapCut D)=nearLeft D := by
    unfold nearLeft nearRight strictA strictB
    rw [dSwap]
    ext z
    simp [depth,min_comm]
  have aSwap : EA (swapCut D)=EB D := by unfold EA EB aPorts bPorts; rw [shD]
  have bSwap : EB (swapCut D)=EA D := by unfold EA EB aPorts bPorts; rw [shD]
  exact bad (two_balance_oriented (S:=swapCut S) (D:=swapCut D) hc ab.symm even conn degree
    (fun h=>sd (swapCut.injective h)) (fun zb za=>by rw [shS,shD]; exact cover za zb)
    (shS.symm ▸ one) (shD.symm ▸ d13) (vSwap.symm ▸ v6) (qSwap.symm ▸ q2)
    (aSwap.symm ▸ be) (bSwap.symm ▸ ae) (lSwap.symm ▸ r) (rSwap.symm ▸ l))

#print axioms traceable_of_adjacent_singleton_thirteen_six_visible
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
