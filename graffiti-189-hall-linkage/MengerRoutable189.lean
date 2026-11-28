import FanRoutable189
import AlmostRoutable189
import Lax17Proofs.Source.HallHooks189
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.ActiveStarHeight Graffiti189LongestPath.OneSlack
open Graffiti189LongestPath.FanRoutable Graffiti189LongestPath.AlmostRoutable
open private Graffiti189LongestPath.boundary_card_of_connectivity Graffiti189LongestPath.no_endpoints from SmallSeparator189
open private Graffiti189LongestPath.Rigidity.mem_omittedStar from Rigidity189
set_option warningAsError true
namespace Graffiti189LongestPath.MengerRoutable
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] [DecidableRel G.Adj] in
/-- A longest path omitting a vertex in a k-connected graph has at least k
vertices. Removing its other vertices cannot isolate its first endpoint. -/
theorem support_large (k : Nat)
    (conn : ∀ S : Finset V,S.card<k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    {a b x : V} {p : G.Walk a b} (hp : IsLongest p) (hx : x∉p.support) :
    k≤p.support.toFinset.card := by
  classical
  let B := p.support.toFinset.erase a
  have xb : x∉B := fun h => hx (List.mem_toFinset.mp (mem_erase.mp h).2)
  have xa : x∉({a}:Finset V) := fun h => hx (mem_singleton.mp h ▸ p.start_mem_support)
  have dis : Disjoint ({a}:Finset V) B := disjoint_left.mpr (fun _ s b =>
    (mem_erase.mp b).1 (mem_singleton.mp s))
  have cl : ∀ u∈({a}:Finset V),∀ v∉({a}:Finset V),G.Adj u v → v∈B := by
    intro u hu v hv e
    have ua : u=a := mem_singleton.mp hu
    subst u
    have vv : v∈p.support := by
      apply Classical.byContradiction
      intro no
      exact (Graffiti189LongestPath.no_endpoints hp no).1 e.symm
    exact mem_erase.mpr ⟨fun h => hv (mem_singleton.mpr h),List.mem_toFinset.mpr vv⟩
  exact (Graffiti189LongestPath.boundary_card_of_connectivity k conn
    (mem_singleton_self a) xa xb dis cl).trans card_erase_le

/-- Exact closed branch: the separated-double star of a counterexample
cannot be Hamilton-connected, even when some of its cut ports are
outside the longest path. -/
theorem routable_double_branch_impossible (hc : G.Connected) (k : Nat) (hk : 6≤k)
    (cap : ∀ v, (EvenFrom G v).card≤k+3)
    (conn : ∀ S : Finset V, S.card<k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    {a b x y : V} {p : G.Walk a b} (hp : IsLongest p) (hx : x∉p.support)
    (hy : y∉p.support) (xy : G.Adj x y) (high : k+2≤G.degree x)
    (double : (Pins p x).card=2) (sep : PairedPins p x=∅)
    (routes : ∀ u∈OmittedStar p x,∀ v∈OmittedStar p x,u≠v →
      ∃ q : G.Walk u v,q.IsPath ∧ (∀ w∈q.support,w∈OmittedStar p x) ∧
        q.length+1=(OmittedStar p x).card) : False := by
  have eq := star_card_degree_and_pins hp hx
  have large : k≤(OmittedStar p x).card := by omega
  have ao : ∀ z∈OmittedStar p x,z∉p.support := fun _ h =>
    (Graffiti189LongestPath.Rigidity.mem_omittedStar.mp h).1
  obtain ⟨F⟩ := hooks_of_small_deletion_connectivity (OmittedStar p x) k hp ao
    large (support_large k conn hp hx) conn
  exact routable_double_no_fan hc k hk cap conn hp hx hy xy high double sep routes F

/-- Weighted extension: even shorter terminal routes can contradict the
order budget when enough boundary ports lie off the longest path. -/
theorem almost_routable_double_branch_impossible (hc : G.Connected) (k : Nat) (hk : 6≤k)
    (cap : ∀ v, (EvenFrom G v).card≤k+3)
    (conn : ∀ S : Finset V, S.card<k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    {a b x y : V} {p : G.Walk a b} (hp : IsLongest p) (hx : x∉p.support)
    (hy : y∉p.support) (xy : G.Adj x y) (high : k+2≤G.degree x)
    (double : (Pins p x).card=2) (sep : PairedPins p x=∅)
    (H : Nat)
    (routes : ∀ u∈OmittedStar p x,∀ v∈OmittedStar p x,u≠v →
      ∃ q : G.Walk u v,q.IsPath ∧ (∀ w∈q.support,w∈OmittedStar p x) ∧ H≤q.length+1)
    (extra : k*(k+2)<(k+1)*H+2*(External G (OmittedStar p x)\p.support.toFinset).card) : False := by
  have eq := star_card_degree_and_pins hp hx
  have large : k≤(OmittedStar p x).card := by omega
  have ao : ∀ z∈OmittedStar p x,z∉p.support := fun _ h =>
    (Graffiti189LongestPath.Rigidity.mem_omittedStar.mp h).1
  have sat : (External G (OmittedStar p x)).card=k := by
    obtain ⟨_,_,alt⟩ := double_porter_saturated_one_slack hc k hp hx double (cap x) conn hy xy
    rcases alt with h|h
    · exact h.2
    · simp [sep] at h
  obtain ⟨F⟩ := hooks_of_small_deletion_connectivity (OmittedStar p x) k hp ao
    large (support_large k conn hp hx) conn
  exact almost_routable_double_no_fan hc k hk cap conn hp hx hy xy high double sep H routes sat extra F

#print axioms support_large
#print axioms routable_double_branch_impossible
#print axioms almost_routable_double_branch_impossible
end Graffiti189LongestPath.MengerRoutable