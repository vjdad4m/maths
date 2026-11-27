import BagProtection180
import DominatingPins180

set_option warningAsError true
namespace Minimal180.Transversals
open Finset SimpleGraph Graffiti177 Graffiti318 Rooted180 Converse180 Assembly180 Substitution
open Classical
variable {V B : Type*} [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]
variable {H : SimpleGraph V} {G : SimpleGraph B} {f : V→B}

/-- Single-marking transfer for arbitrary nonempty substitution bags.
A universal vertex in the quotient supplies a dominating edge upstairs. -/
theorem substitution_protection (h : Bags H G f) (gc : G.Connected) (hn : 1<Fintype.card B)
    (r : V) (p : Bool) (A : Finset V) (ai : Indep H A) (old : Protected G (f r) p (A.image f)) :
    Protected H r p A := by
  classical
  by_cases hub : ∃ i,Universal G i
  · obtain ⟨i,top⟩ := hub
    obtain ⟨y,ed⟩ := h.hubEdge gc hn top r
    have n := Fintype.card_le_of_surjective _ h.onto
    exact dominating_protection H (h.connected gc hn) (by omega) ed p A ai
  · exact protected_lift h gc hn (fun i u => hub ⟨i,u⟩) r p A ai old

theorem protected_ordinary (G : SimpleGraph V) (gc : G.Connected)
    (good : ∀ r p A,Indep G A → Protected G r p A) :
    1+independence G+maxEven G≤maxLeaves G+bipartiteNum G := by
  apply ordinary_of_rooted G gc
  intro r p A ai
  obtain ⟨Z,col,_,pay⟩ := good r p A ai
  exact pay.trans (Nat.add_le_add_left (size_bip G col) _)

/-- The bags have arbitrary internal graphs and arbitrary nonzero sizes.
An apex quotient or a quotient satisfying GoodPair yields the stronger
rooted witness upstairs and hence the original unrooted inequality. -/
theorem substitution_class (h : Bags H G f) (gc : G.Connected) (hn : 1<Fintype.card B)
    (base : Fintype.card B≤bipartiteNum G+1 ∨ ∃ a b,GoodPair G a b) :
    (∀ r p A,Indep H A → Protected H r p A) ∧ (∀ r,PrimeTests H r) ∧
      1+independence H+maxEven H≤maxLeaves H+bipartiteNum H := by
  have good (r : V) (p : Bool) (A : Finset V) (ai : Indep H A) : Protected H r p A := by
    apply substitution_protection h gc hn r p A ai
    have ii := h.indSupport A ai
    rcases base with rk|⟨a,b,pair⟩
    · exact protected_rank_one G gc hn rk (f r) p _ ii
    · exact protected_pair G gc hn a b pair (f r) p _ ii
  exact ⟨good,fun r => protected_tests H r (good r),protected_ordinary H (h.connected gc hn) good⟩

#print axioms substitution_protection
#print axioms protected_ordinary
#print axioms substitution_class
end Minimal180.Transversals
