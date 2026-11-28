import FanPorts189
import SingleFourthBudget189
import MengerRoutable189
import MarkedRoutable189
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.ActiveStarHeight Graffiti189LongestPath.OneSlack
open Graffiti189LongestPath.FanRoutable Graffiti189LongestPath.FanWeighted Graffiti189LongestPath.FanPorts
open Graffiti189LongestPath.SingleFourthBudget Graffiti189LongestPath.MengerRoutable
open Graffiti189LongestPath.HookMark Graffiti189LongestPath.FanGain
open private Graffiti189LongestPath.Rigidity.mem_omittedStar Graffiti189LongestPath.Rigidity.mem_external from Rigidity189
open scoped BigOperators
set_option warningAsError true
namespace Graffiti189LongestPath.SingleRadiusRoutable
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Terminal paths need not span the star. Their common guaranteed order H
and the count of off-path ports jointly rule out the single exact-cut branch. -/
theorem single_terminal_order_impossible (hc : G.Connected) (k : Nat) (hk : 6≤k)
    (cap : ∀ v, (EvenFrom G v).card≤k+3)
    (conn : ∀ S : Finset V, S.card<k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    {a b x : V} {p : G.Walk a b} (hp : IsLongest p) (hx : x∉p.support)
    (high : k+2≤G.degree x)
    (one : (Pins p x).card=1) (sat : (External G (OmittedStar p x)).card=k)
    (rad : ∀ z,G.dist x z≤4)
    (H : Nat)
    (routes : ∀ u∈OmittedStar p x,∀ v∈OmittedStar p x,u≠v →
      ∃ q : G.Walk u v,q.IsPath ∧ (∀ w∈q.support,w∈OmittedStar p x) ∧ H≤q.length+1)
    (extra : k*(k+2)<(k+1)*H+2*(External G (OmittedStar p x)\p.support.toFinset).card) : False := by
  let A := OmittedStar p x
  let B := External G A
  have ao : ∀ z∈A,z∉p.support := fun _ z =>
    (Graffiti189LongestPath.Rigidity.mem_omittedStar.mp z).1
  have cA : ∀ u∈A,∀ v∉A,G.Adj u v → v∈B := fun u hu v hv ed =>
    Graffiti189LongestPath.Rigidity.mem_external.mpr ⟨hv,u,hu,ed⟩
  have ab : Disjoint A B := disjoint_left.mpr fun _ hu hv =>
    (Graffiti189LongestPath.Rigidity.mem_external.mp hv).1 hu
  have eq := star_card_degree_and_pins hp hx
  have big : 1<A.card := by
    change A.card+(Pins p x).card=G.degree x+1 at eq
    omega
  have large : k≤A.card := by
    change A.card+(Pins p x).card=G.degree x+1 at eq
    omega
  obtain ⟨F⟩ := hooks_of_small_deletion_connectivity A k hp ao large (support_large k conn hp hx) conn
  have low := weighted_hooked_lower k (by omega) hp H A ao big routes F
  have long := off_path_ports_le_total_hook_length A B k sat ab cA hp F ao
  have up := single_star_order_upper_radius_four hc k hk cap conn hp hx high one sat rad
  change Fintype.card V≤A.card+k+k*(k+2) at up
  change k*(k+2)<(k+1)*H+2*(B\p.support.toFinset).card at extra
  omega

#print axioms single_terminal_order_impossible
/-- With at least k/2 cut ports outside P, a base terminal order k is
enough if one mark with a cut neighbor always adds one further vertex
to paths ending at it. That mark can be made one of the fan roots. -/
theorem single_marked_order_impossible (hc : G.Connected) (k : Nat) (hk : 6≤k)
    (cap : ∀ v,(EvenFrom G v).card≤k+3)
    (conn : ∀ S : Finset V,S.card<k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    {a b x w z : V} {p : G.Walk a b} (hp : IsLongest p) (hx : x∉p.support)
    (high : k+2≤G.degree x)
    (one : (Pins p x).card=1) (sat : (External G (OmittedStar p x)).card=k)
    (rad : ∀ z,G.dist x z≤4)
    (wa : w∈OmittedStar p x) (zb : z∈External G (OmittedStar p x)) (wz : G.Adj w z)
    (pay : k≤2*(External G (OmittedStar p x)\p.support.toFinset).card+1)
    (outer : ∀ u∈OmittedStar p x,∃ (v:V) (q:G.Walk u v),q.IsPath ∧
      (∀ z∈q.support,z∈OmittedStar p x) ∧ k+(if u=w then 1 else 0)≤q.length+1)
    (between : ∀ u∈OmittedStar p x,∀ v∈OmittedStar p x,u≠v →
      ∃ q : G.Walk u v,q.IsPath ∧ (∀ z∈q.support,z∈OmittedStar p x) ∧
        k+(if u=w then 1 else 0)+(if v=w then 1 else 0)≤q.length+1) : False := by
  classical
  let A := OmittedStar p x
  let B := External G A
  have eq := star_card_degree_and_pins hp hx
  change A.card+(Pins p x).card=G.degree x+1 at eq
  have large : k≤A.card := by omega
  have ao : ∀ z∈A,z∉p.support := fun _ h => (Graffiti189LongestPath.Rigidity.mem_omittedStar.mp h).1
  change B.card=k at sat
  obtain ⟨F⟩ := hooks_of_small_deletion_connectivity A k hp ao large (support_large k conn hp hx) conn
  have ab : Disjoint A B := disjoint_left.mpr fun _ hu hv =>
    (Graffiti189LongestPath.Rigidity.mem_external.mp hv).1 hu
  have cA : ∀ u∈A,∀ v∉A,G.Adj u v → v∈B := fun u hu v hv ed =>
    Graffiti189LongestPath.Rigidity.mem_external.mpr ⟨hv,u,hu,ed⟩
  obtain ⟨N,i,mark⟩ := marked_hook_family A B k sat ab cA hp F ao wa zb wz
  let e (v : V) := if v=w then (1:Nat) else 0
  have low := endpoint_gain_hooked_lower k (by omega) hp k A ao e outer between N
  have up := single_star_order_upper_radius_four hc k hk cap conn hp hx high one sat rad
  change Fintype.card V≤A.card+k+k*(k+2) at up
  have lng := off_path_ports_le_total_hook_length A B k sat ab cA hp N ao
  change k≤2*(B\p.support.toFinset).card+1 at pay
  have bg : 1≤∑ j : Fin k,e (N.root j) := by
    have n : e (N.root i)=1 := by simp [e,mark]
    rw [←n]
    exact single_le_sum (fun (a : Fin k) _ => Nat.zero_le (e (N.root a))) (mem_univ i)
  have id : k*(k+2)=(k+1)*k+k := by rw [Nat.mul_add,Nat.add_mul,one_mul]; omega
  rw [id] at up
  omega

#print axioms single_marked_order_impossible
end Graffiti189LongestPath.SingleRadiusRoutable
