import PairClauses180

set_option warningAsError true
namespace Minimal180.PairRepair
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 Substitution Transversals
open Classical
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- In the large-budget branch, all ends of all minimum transversals
must be pinned simultaneously. In the other branch all pinned vertices
have degree at most four. -/
def SharedCover (G : SimpleGraph V) (K : Finset V) : Prop := PairCover G K ∧
  ((∀ x∈K,G.degree x≤4) ∨
    ∀ a b,TransPair G a b → a∈K ∧ b∈K ∧
      ∀ c : V→Bool,ProperOn G (univ\{a,b}) c → ∀ i j,3<(sideNeighbors G a c i∪sideNeighbors G b c j).card)

theorem shared_failure (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V) (r : V) (p : Bool)
    (A : Finset V) (ai : Indep G A) (bad : ¬Protected G r p A) :
    SharedCover G (A∩insert r (parity G r p)) := by
  classical
  let K := A∩insert r (parity G r p)
  let B := allowance G r p A
  have cov := failed_cover G gc hn r p A ai bad
  refine ⟨cov,?_⟩
  by_cases small : B≤2
  · left
    have high : 2<Fintype.card V := by
      by_contra! low;exact bad (protected_bip G gc hn (bip_of_short G hn low) r p A ai)
    intro x xm
    have cost := protected_degree G gc high r x p A ai xm
    change allowance G r p A≤2 at small;omega
  · right
    have both {x y : V} (pair : TransPair G x y) : y∈K := by
      by_contra miss
      have xm := (cov.2 x y pair).1.resolve_right miss
      have fix := (solo_rigidity G gc hn r p A ai bad x y pair.1 pair.2 xm miss).2.1
      exact small (by change allowance G r p A≤2;omega)
    intro a b h
    have bk := both h
    have ak := both (x:=b) (y:=a) ⟨h.1.symm,by simpa only [pair_comm b a] using h.2⟩
    refine ⟨ak,bk,fun c cp i j => ?_⟩
    have bound := double_rigidity G gc hn r p A ai bad a b h.1 ak bk c cp i j
    change ¬allowance G r p A≤2 at small;omega

/-- Outside the marked root all pins must have the same distance parity.
If no simultaneous shared cover satisfies that restriction, all markings
at this particular root and parity are settled. -/
theorem parity_excludes (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V) (r : V) (p : Bool)
    (no : ∀ K⊆insert r (parity G r p),¬SharedCover G K) (A : Finset V) (ai : Indep G A) : Protected G r p A := by
  by_contra bad;exact no _ inter_subset_right (shared_failure G gc hn r p A ai bad)

theorem tests_of_parity (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V) (r : V)
    (no : ∀ p K,K⊆insert r (parity G r p) → ¬SharedCover G K) : PrimeTests G r :=
  protected_tests G r (fun p => parity_excludes G gc hn r p (no p))

theorem universal_iff_shared_remainder : Assembly180.Universal.{u} ↔
    ∀ (W : Type u) [Fintype W] [DecidableEq W] (G : SimpleGraph W),G.Connected →
      2<Fintype.card W → Prime G → bipartiteNum G+1<Fintype.card W → (∀ a b,¬GoodPair G a b) →
      ∀ r,(∀ y,¬DomEdge G r y) →
        (∃ p K,K⊆insert r (parity G r p) ∧ SharedCover G K) → PrimeTests G r := by
  constructor
  · intro all W _ _ G gc high _ _ _ r no _;exact universal_prime_tests all G gc high r no
  · intro rest
    apply universal_iff_remaining_tests.mpr
    intro W _ _ G gc high prime rank pair r no
    by_cases yes : ∃ p K,K⊆insert r (parity G r p) ∧ SharedCover G K
    · exact rest W G gc high prime rank pair r no yes
    · exact tests_of_parity G gc (by omega) r (fun p K sub cover => yes ⟨p,K,sub,cover⟩)

#print axioms shared_failure
#print axioms parity_excludes
#print axioms tests_of_parity
#print axioms universal_iff_shared_remainder
end Minimal180.PairRepair
