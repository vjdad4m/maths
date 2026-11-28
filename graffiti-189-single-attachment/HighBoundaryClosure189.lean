import HighDichotomy189
import SingleRadiusClosure189
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
open Graffiti189LongestPath.Normalize Graffiti189LongestPath.HighDichotomy
open Graffiti189LongestPath.SingleStar Graffiti189LongestPath.SingleRadiusClosure
open Graffiti189LongestPath.PosaOneLow
open private Graffiti189LongestPath.pin_data from SmallSeparator189
set_option warningAsError true
namespace Graffiti189LongestPath.HighBoundaryClosure
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- At d≥12 and connectivity at least d−2, any nontraceable graph in
the conjecture domain must admit a high singleton root with a genuinely
oversized boundary. Neither exact-cut singleton radius is needed. -/
theorem forced_oversized_single_at_d12 (hc : G.Connected) (k : Nat) (hk : 10≤k)
    (cap : ∀ v,(EvenFrom G v).card≤k+3)
    (conn : ∀ S : Finset V,S.card<k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (deg : ∀ u v : V,u≠v → k+2≤G.degree u ∨ k+2≤G.degree v)
    (fail : ¬∃ (u v : V) (q : G.Walk u v),q.IsPath ∧ ∀ z,z∈q.support) :
    ∃ (a b : V) (p : G.Walk a b) (x : V), EdgeMinAvoid (k+2) p ∧ x∉p.support ∧
      k+2≤G.degree x ∧ (Pins p x).card=1 ∧ (External G (OmittedStar p x)).card=k+1 ∧
      (Shell G x 4).card=0 ∧ (DistanceTwo G x \ External G (OmittedStar p x))=FlankVertices p x := by
  obtain ⟨a,b,p,x,hp,hx,high,h⟩ := normalized_attachment_dichotomy hc k (by omega) cap conn deg fail
  rcases h with ⟨one,_,rad⟩ | ⟨two,sep,_,_,_⟩
  · have budget := singleton_star_budget hc k conn hp.1.1 hx one (cap x)
    have big : (External G (OmittedStar p x)).card=k+1 := by
      by_contra! neq
      have sat : (External G (OmittedStar p x)).card=k := by
        have l := budget.1
        have u := budget.2.1
        omega
      exact single_radius_four_exact_cut_impossible hc k (by omega) cap conn deg fail hp hx high one sat rad
    have extra := budget.2.2.2.2.2 big
    exact ⟨a,b,p,x,hp,hx,high,one,big,extra⟩
  have ⟨i,hi⟩ := card_pos.mp (by omega : 0<(Pins p x).card)
  obtain ⟨y,xy,hy⟩ := omitted_has_omitted_neighbor hc hp.1.1 hx high ⟨_,(Graffiti189LongestPath.pin_data hi).2⟩
    (distanceTwo_le_of_even _ _ (cap x))
  exact (separated_double_d12_impossible hc k hk cap conn deg fail hp hx hy xy two sep high).elim

#print axioms forced_oversized_single_at_d12
end Graffiti189LongestPath.HighBoundaryClosure
