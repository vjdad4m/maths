import CriticalOffPath189
import NearFullCycle189
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack Graffiti189LongestPath.Normalize
open Graffiti189LongestPath.CriticalOffPath Graffiti189LongestPath.NearFullCycle
set_option warningAsError true
namespace Graffiti189LongestPath.MinimalCycleBound
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Exact remaining cycle-length ceiling at minimum star height. In the
odd-height case this meets the ordinary one-low Dirac lower bound,
reducing that case to the equality geometry of a cycle missing two vertices. -/
theorem minimum_height_cycles_le_order_sub_two (hc : G.Connected) (k : Nat) (hk : 7≤k)
    (cap : ∀ v,(EvenFrom G v).card≤k+3)
    (conn : ∀ S : Finset V,S.card<k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (deg : ∀ u v : V,u≠v → k+2≤G.degree u ∨ k+2≤G.degree v)
    (fail : ¬∃ (u v : V) (q : G.Walk u v),q.IsPath ∧ ∀ z,z∈q.support)
    {a b x y : V} {p : G.Walk a b} (hp : EdgeMinAvoid (k+2) p) (hx : x∉p.support)
    (hy : y∉p.support) (xy : G.Adj x y)
    (double : (Pins p x).card=2) (sep : PairedPins p x=∅)
    (high : k+2≤G.degree x)
    (large : 10<(OmittedStar p x).card) (height : (OmittedStar p x).card=k+1)
    {r : ↥(((OmittedStar p x).erase x : Finset V) : Set V)}
    (c : (G.induce (((OmittedStar p x).erase x : Finset V) : Set V)).Walk r r)
    (cc : c.IsCycle) :
    c.length+2≤k := by
  have crit := separated_double_critical_ports hc k hk cap conn deg fail hp hx hy xy double sep high
  have pay : k≤2*(External G (OmittedStar p x)\p.support.toFinset).card+1 := by omega
  apply Nat.le_of_not_gt
  intro cl
  exact minimum_height_no_near_full_cycle hc k (by omega) cap conn deg fail hp.1.1
    hx hy xy high double sep large height pay ⟨r,c,cc,by omega⟩

#print axioms minimum_height_cycles_le_order_sub_two
end Graffiti189LongestPath.MinimalCycleBound
