import SixSingletonQ1Symmetric189
import SixSingletonAdjacentZeroComplete189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph Finset ArticulationPair Graffiti189Ore
open private Shore from AdjacentCutFiveActual189
open private Cmp aPorts bPorts DeletionConnected from SixCutFar189
open private Vis from AdjacentCutFiveComponents189
open private Dark strictA strictB bal from SixSingletonGeometry189
open private nearLeft nearRight nearBal from SixSingletonFiveGeometry189
open private EA EB from SixSingletonMultiZeroGeom189
open private swapCut from AdjacentCutFiveMixedNineGeom189
open FiveAdjacent (shore_swapCut depth)
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

theorem adjacent_six_counterexample_exact_two_balance_shape
    (hc : G.Connected) (ab : G.Adj a b) (even : ∀ z,(EvenFrom G z).card≤7)
    (conn : DeletionConnected G) (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {S D : Cmp G a b} (sd : S≠D)
    (cover : ∀ {z : V},z≠a → z≠b → z∈Shore S ∨ z∈Shore D)
    (one : (Shore S).card=1) (d13 : (Shore D).card=13) (v6 : (Vis D).card=6)
    (bad : ¬Traceable G) :
    (nearBal D).card=2 ∧
    (((EA D).card=1 ∧ (EB D).card=2 ∧ (nearLeft D).card=2 ∧ (nearRight D).card=3) ∨
    ((EA D).card=2 ∧ (EB D).card=1 ∧ (nearLeft D).card=3 ∧ (nearRight D).card=2)) := by
  classical
  have qpos : 0<(nearBal D).card := by
    by_contra h
    exact bad (traceable_of_adjacent_singleton_thirteen_six_zero_balance
      hc ab even conn degree sd cover one d13 v6 (by omega))
  have qn : (nearBal D).card≠1 := fun h=>bad (traceable_of_adjacent_singleton_thirteen_six_one_balance
    hc ab even conn degree sd cover one d13 v6 h)
  have ⟨la,ua,lb,ub⟩ : 1≤(EA D).card ∧ (EA D).card≤2 ∧ 1≤(EB D).card ∧ (EB D).card≤2 := by
    rcases adjacent_singleton_thirteen_visible_profile hc ab even conn degree sd cover one d13 with
       ⟨m,_,_,_⟩|⟨_,p,q,r,t,_⟩
    · omega
    exact ⟨p,q,r,t⟩
  by_cases b2 : (EB D).card=2
  · have h := adjacent_six_positive_profile_counts hc ab even conn degree sd cover one d13 v6 b2 qpos
    change ((EA D).card=2 ∧ (nearBal D).card=1 ∧ _) ∨
      ((EA D).card=1 ∧ (nearBal D).card=1 ∧ _) ∨
      ((EA D).card=1 ∧ (nearBal D).card=2 ∧ (nearLeft D).card=2 ∧ (nearRight D).card=3) at h
    rcases h with ⟨_,e,_⟩|⟨_,e,_⟩|⟨x,q,l,r⟩
    · exact (qn e).elim
    · exact (qn e).elim
    exact ⟨q,.inl ⟨x,b2,l,r⟩⟩
  have b1 : (EB D).card=1 := by omega
  have a2 : (EA D).card=2 := by
    by_contra h
    have a1 : (EA D).card=1 := by omega
    exact bad (traceable_of_adjacent_singleton_thirteen_unique hc ab even conn degree sd cover one d13 v6 a1 b1)
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
  have b2s : (EB (swapCut D)).card=2 := by rw [bSwap,a2]
  have hs := adjacent_six_positive_profile_counts (S:=swapCut S) (D:=swapCut D) hc ab.symm even conn degree
    (fun h=>sd (swapCut.injective h)) (fun zb za=>by rw [shS,shD]; exact cover za zb)
    (shS.symm ▸ one) (shD.symm ▸ d13) (vSwap.symm ▸ v6) b2s (qSwap.symm ▸ qpos)
  change ((EA (swapCut D)).card=2 ∧ (nearBal (swapCut D)).card=1 ∧ _) ∨
    ((EA (swapCut D)).card=1 ∧ (nearBal (swapCut D)).card=1 ∧ _) ∨
    ((EA (swapCut D)).card=1 ∧ (nearBal (swapCut D)).card=2 ∧
      (nearLeft (swapCut D)).card=2 ∧ (nearRight (swapCut D)).card=3) at hs
  rw [aSwap,qSwap,lSwap,rSwap] at hs
  rcases hs with ⟨_,e,_⟩|⟨_,e,_⟩|⟨_,q,r,l⟩
  · exact (qn e).elim
  · exact (qn e).elim
  exact ⟨q,.inr ⟨a2,b1,l,r⟩⟩

#print axioms adjacent_six_counterexample_exact_two_balance_shape
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
