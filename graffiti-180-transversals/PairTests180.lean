import PairObstruction180

set_option warningAsError true
namespace Minimal180.Transversals
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 Substitution
open Classical
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- One graph-wide sufficient condition for both uncredited tests. -/
def GoodPair (G : SimpleGraph V) (a b : V) : Prop :=
  a≠b ∧ TwoColor G (univ\{a,b}) ∧
    (G.Adj a b ∨ (G.degree a≠4 ∧ G.degree b≠4 ∧
      (G.degree b+2<G.degree a+(G.neighborFinset a∩G.neighborFinset b).card ∨
       G.degree a+2<G.degree b+(G.neighborFinset a∩G.neighborFinset b).card ∨
       (G.neighborFinset a∪G.neighborFinset b).card<6)))

theorem protected_pair (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    (a b : V) (pair : GoodPair G a b) (r : V) (p : Bool) (A : Finset V) (ai : Indep G A) :
    Protected G r p A := by
  by_contra no
  obtain ⟨ab,bi,law⟩ := pair
  obtain ⟨ne,shape⟩ := pair_obstruction G gc hn r p A ai no a b ab bi
  obtain ⟨da,db,rest⟩ := law.resolve_left ne
  rcases shape with ⟨_,_,four⟩|⟨_,_,four⟩|⟨_,_,la,lb,large⟩
  · exact da four
  · exact db four
  · rcases rest with h|h|h <;> omega

/-- Deleting the endpoints of a single edge may remove arbitrarily many
odd cycles. This condition suffices for both tests at every root. -/
theorem prime_tests_edge_transversal (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    {a b : V} (edge : G.Adj a b) (bi : TwoColor G (univ\{a,b})) (r : V) : PrimeTests G r :=
  protected_tests G r (protected_pair G gc hn a b ⟨edge.ne,bi,Or.inl edge⟩ r)

theorem prime_tests_good_pair (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    (a b : V) (pair : GoodPair G a b) (r : V) : PrimeTests G r :=
  protected_tests G r (protected_pair G gc hn a b pair r)

/-- In the first outstanding deficit, all transversal pairs are nonedges.
The degree and common-neighbor conditions in GoodPair further restrict
the prime graphs that require testing. -/
theorem universal_iff_remaining_tests : Assembly180.Universal.{u} ↔
    ∀ (W : Type u) [Fintype W] [DecidableEq W] (G : SimpleGraph W),G.Connected →
      2<Fintype.card W → Prime G → bipartiteNum G+1<Fintype.card W → (∀ a b,¬GoodPair G a b) →
      ∀ r,(∀ y,¬DomEdge G r y) → PrimeTests G r := by
  constructor
  · intro all W _ _ G gc high _ _ _ r no;exact universal_prime_tests all G gc high r no
  · intro test
    apply universal_iff_prime_deficit_two_or_more.mpr
    intro W _ _ G gc high prime rank r no
    by_cases good : ∃ a b,GoodPair G a b
    · obtain ⟨a,b,pair⟩ := good
      exact prime_tests_good_pair G gc (by omega) a b pair r
    · exact test W G gc high prime rank (fun a b h => good ⟨a,b,h⟩) r no

#print axioms protected_pair
#print axioms prime_tests_edge_transversal
#print axioms prime_tests_good_pair
#print axioms universal_iff_remaining_tests
end Minimal180.Transversals
