import SeparatedRootReduction189
import OversizedRoutable189
import OversizedShore189
import DefectiveTerminal189
import GroupedLitBudget189
import OversizedLitBudget189
import OversizedCriticalVertex189
import OversizedClosure189
import HighBoundaryClosure189
import OffPathBoundaryBudget189
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack Graffiti189LongestPath.ActiveStarHeight
open Graffiti189LongestPath.Normalize Graffiti189LongestPath.ExactStarShore Graffiti189LongestPath.TwoShoreTight
open Graffiti189LongestPath.OversizedRoutable Graffiti189LongestPath.OversizedShore
open Graffiti189LongestPath.DefectiveCharge Graffiti189LongestPath.DefectiveTerminal
open Graffiti189LongestPath.GroupedLitBudget Graffiti189LongestPath.OversizedCriticalVertex
open Graffiti189LongestPath.OversizedLitBudget Graffiti189LongestPath.HighBoundaryClosure
open Graffiti189LongestPath.PosaOneLow Graffiti189LongestPath.SingleHeight
open Graffiti189LongestPath.OneExceptionTerminal Graffiti189LongestPath.MengerRoutable Graffiti189LongestPath.OffPathBoundaryBudget
open private Graffiti189LongestPath.Rigidity.mem_external Graffiti189LongestPath.Rigidity.mem_omittedStar from Rigidity189
open private Graffiti189LongestPath.boundary_card_of_connectivity Graffiti189LongestPath.no_endpoints Graffiti189LongestPath.pin_data from SmallSeparator189
set_option warningAsError true
set_option maxHeartbeats 3000000
open Graffiti189LongestPath.OversizedClosure
namespace Graffiti189LongestPath.GroupedOversizedClosure
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Universal high-connectivity closure when the second-smallest
degree is at least 13. The parity bound and connectivity are the only
graph-invariant premises; all attachment cases are discharged. -/
theorem traceable_of_high_connectivity_d13 (hc : G.Connected) (k : Nat) (hk : 11≤k)
    (cap : ∀ v,(EvenFrom G v).card≤k+3)
    (conn : ∀ S : Finset V,S.card<k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (deg : ∀ u v : V,u≠v → k+2≤G.degree u ∨ k+2≤G.degree v) :
    ∃ (u v : V) (q : G.Walk u v),q.IsPath ∧ ∀ z,z∈q.support := by
  classical
  apply Classical.byContradiction
  intro fail
  obtain ⟨a,b,p,x,hp,hx,high,one,sat,_,_⟩ := forced_oversized_single_at_d12 hc k (by omega) cap conn deg fail
  let A := OmittedStar p x
  let B := External G A
  have hmin : k+2≤A.card := by
    have e := star_card_degree_and_pins hp.1.1 hx
    change A.card+(Pins p x).card=G.degree x+1 at e
    omega
  obtain ⟨i,hi⟩ := card_pos.mp (by omega : 0<(Pins p x).card)
  have hmax : A.card≤k+4 := Nat.le_of_not_gt (fun r => fail
    (traceable_of_tall_singleton hc k (by omega) cap conn deg hp.1.1 hx one hi r))
  have rad (z : V) : G.dist x z≤4 := by
    by_contra! far
    have g := shell_card_of_far hc k conn (x:=x) (y:=z) (i:=4) (by decide) (by omega)
    have bud := Graffiti189LongestPath.SingleStar.singleton_star_budget hc k conn hp.1.1 hx one (cap x)
    have zz := ((bud.2.2.2.2.2) sat).1
    omega
  have upper := oversized_single_lit_order_upper hc k (by omega)
    cap conn hp.1.1 hx high one hmax sat rad
  obtain ⟨w,wd,wh⟩ := oversized_critical_vertex hc k (by omega)
    cap conn deg fail hp hx high one sat upper
  have save := oversized_single_grouped_budget hc k hk cap conn hp.1.1 hx high one hmax sat rad ⟨w,wd,wh⟩
  change Fintype.card V+k+2*(k-1)≤2*A.card+k*(k+2)+9 at save
  let off := (B\p.support.toFinset).card
  have wo := (Graffiti189LongestPath.Rigidity.mem_omittedStar.mp w.property).1
  have pins : (Pins p w.val).card≤2 := by
    by_cases e : (Pins p w.val).card=0
    · omega
    obtain ⟨j,hj⟩ := card_pos.mp (by omega : 0<(Pins p w.val).card)
    have bound := (normalized_high_omission hc (k+2) k (by omega) le_rfl cap conn hp wo wh j hj).1
    omega
  have bd := degree_le_shore_and_ports hp.1.1 A w wo
  change G.degree w.val≤(G.induce (A:Set V)).degree w+(Pins p w.val).card+off at bd
  change (G.induce (A:Set V)).degree w≤A.card/2 at wd
  have crit : k≤A.card/2+off := by omega
  obtain ⟨v,c,cc,cl⟩ := oversized_root_deleted_long_cycle hc k (by omega) cap conn deg fail hp hx one sat high
  change 2*((A.card-1)/2-1)≤c.length at cl
  by_cases len : k-1≤c.length
  · have up : Fintype.card V<A.card+k+(k+1)*k+2*(off-1) := by
      have id : k+(k+1)*k=k*(k+2) := by
        have a : (k+1)*k=k*k+k := by rw [Nat.add_mul,one_mul]
        have b : k*(k+2)=k*k+2*k := by rw [Nat.mul_add,Nat.mul_comm k 2]
        omega
      omega
    exact oversized_no_long_shore_cycle hc k (by omega) cap conn deg fail hp.1.1
      hx one sat (show 12<A.card by omega) (k-1) (show k≤A.card by omega) (by
        rw [show k-1+1=k by omega]
        exact up) ⟨v,c,cc,by omega⟩
  have ht : A.card=k+2 := by omega
  have up : Fintype.card V<A.card+k+(k+1)*(k-1)+2*(off-1) := by
    have id : k+(k+1)*(k-1)+k+1=k*(k+2) := by
      have e : (k+1)*(k-1)+(k+1)=(k+1)*k := by
        calc
          _ = (k+1)*(k-1+1) := by rw [Nat.mul_add,Nat.mul_one]
          _ = _ := by rw [show k-1+1=k by omega]
      have f : (k+1)*k=k*k+k := by rw [Nat.add_mul,one_mul]
      have g : k*(k+2)=k*k+2*k := by rw [Nat.mul_add,Nat.mul_comm k 2]
      omega
    omega
  exact oversized_no_long_shore_cycle hc k (by omega) cap conn deg fail hp.1.1
    hx one sat (show 12<A.card by omega) (k-2) (show k≤A.card by omega) (by
      rw [show k-2+1=k-1 by omega]
      exact up) ⟨v,c,cc,by omega⟩

#print axioms traceable_of_high_connectivity_d13
end Graffiti189LongestPath.GroupedOversizedClosure
