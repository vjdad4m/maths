import FanPorts189
import DefectiveFanPorts189
import MengerRoutable189
import MarkedRoutable189
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.ActiveStarHeight Graffiti189LongestPath.OneSlack
open Graffiti189LongestPath.FanRoutable Graffiti189LongestPath.FanWeighted Graffiti189LongestPath.FanPorts
open Graffiti189LongestPath.DefectiveFanPorts Graffiti189LongestPath.MengerRoutable
open Graffiti189LongestPath.HookMark Graffiti189LongestPath.FanGain
open private Graffiti189LongestPath.Rigidity.mem_omittedStar Graffiti189LongestPath.Rigidity.mem_external from Rigidity189
open scoped BigOperators
set_option warningAsError true
namespace Graffiti189LongestPath.OversizedRoutable
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Terminal paths need not span the star. Their common guaranteed order H
and the count of off-path ports jointly rule out the single exact-cut branch. -/
theorem oversized_terminal_budget_impossible (k : Nat) (hk : 6≤k)
    (conn : ∀ S : Finset V, S.card<k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    {a b x : V} {p : G.Walk a b} (hp : IsLongest p) (hx : x∉p.support)
    (large : k≤(OmittedStar p x).card) (sat : (External G (OmittedStar p x)).card≤k+1)
    (H : Nat)
    (routes : ∀ u∈OmittedStar p x,∀ v∈OmittedStar p x,u≠v →
      ∃ q : G.Walk u v,q.IsPath ∧ (∀ w∈q.support,w∈OmittedStar p x) ∧ H≤q.length+1)
    (up : Fintype.card V < (OmittedStar p x).card+k+(k+1)*H+
      2*((External G (OmittedStar p x)\p.support.toFinset).card-1)) : False := by
  let A := OmittedStar p x
  let B := External G A
  change k≤A.card at large
  have ao : ∀ z∈A,z∉p.support := fun _ z =>
    (Graffiti189LongestPath.Rigidity.mem_omittedStar.mp z).1
  have cA : ∀ u∈A,∀ v∉A,G.Adj u v → v∈B := fun u hu v hv ed =>
    Graffiti189LongestPath.Rigidity.mem_external.mpr ⟨hv,u,hu,ed⟩
  have ab : Disjoint A B := disjoint_left.mpr fun _ hu hv =>
    (Graffiti189LongestPath.Rigidity.mem_external.mp hv).1 hu
  have big : 1<A.card := by omega
  obtain ⟨F⟩ := hooks_of_small_deletion_connectivity A k hp ao large (support_large k conn hp hx) conn
  have low := weighted_hooked_lower k (by omega) hp H A ao big routes F
  have long := defective_off_path_ports_le_total_hook_length A B k sat ab cA hp F ao
  change Fintype.card V<A.card+k+(k+1)*H+2*((B\p.support.toFinset).card-1) at up
  omega

#print axioms oversized_terminal_budget_impossible
#print axioms oversized_terminal_budget_impossible
end Graffiti189LongestPath.OversizedRoutable
