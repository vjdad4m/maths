import PosaEndpointCycle189
import PosaCycleExtend189
import SeparatedDirac189
import HighEndpoint189
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.PosaEndpointCycle Graffiti189LongestPath.HighEndpoint189
open Graffiti189LongestPath.SeparatedDirac Graffiti189LongestPath.Rigidity
open Graffiti189LongestPath.Normalize Graffiti189LongestPath.OneSlack
set_option warningAsError true
set_option maxHeartbeats 4500000
universe u
namespace Graffiti189LongestPath.PosaOneLow

/-- Pósa's one-low-degree circumference bound in the exact finite
interface needed by the normalized separated-double proof. -/
theorem proved_one_low_circumference : OneLowCircumference.{u} := by
  intro W _ _ H _ m m2 wn conn d2 pair
  classical
  have h0 := conn (∅:Finset W) (by simp)
  have hi : (H.induce Set.univ).Connected := by
    have eq : ((↑(∅ : Finset W) : Set W)ᶜ) = Set.univ := by ext x; simp
    rw [← eq]
    exact h0
  have hc : H.Connected := (SimpleGraph.induceUnivIso H).connected_iff.mp hi
  obtain ⟨a,b,p,hp⟩ := Rigidity.exists_longest hc
  obtain ⟨x,y,q,hq,_,dx,dy⟩ := rotate_to_two_high_endpoints_of_min_two m d2 pair hp
  exact long_cycle_from_high_longest_path m m2 hq dx dy conn
    (fun z c cc len sup => PosaCycleExtend189.spanning_of_longest_path_cycle hq hc c cc sup len)

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Unconditional closure of the high-degree normalized separated-double
branch, with no exterior circumference premise. This is not the full
Graffiti.pc #189 theorem. -/
theorem separated_double_d12_impossible (hc : G.Connected) (k : Nat) (hk : 10≤k)
    (cap : ∀ v,(EvenFrom G v).card≤k+3)
    (conn : ∀ S : Finset V,S.card<k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (deg : ∀ u v : V,u≠v → k+2≤G.degree u ∨ k+2≤G.degree v)
    (fail : ¬∃ (u v : V) (q : G.Walk u v),q.IsPath ∧ ∀ z,z∈q.support)
    {a b x y : V} {p : G.Walk a b} (hp : EdgeMinAvoid (k+2) p) (hx : x∉p.support)
    (hy : y∉p.support) (xy : G.Adj x y)
    (double : (Pins p x).card=2) (sep : PairedPins p x=∅)
    (high : k+2≤G.degree x) : False := by
  exact separated_double_of_one_low_circumference proved_one_low_circumference hc k hk cap conn
    deg fail hp hx hy xy double sep high

#print axioms proved_one_low_circumference
#print axioms separated_double_d12_impossible
end Graffiti189LongestPath.PosaOneLow
