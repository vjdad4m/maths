import PairColors180
import InflationTests180

set_option warningAsError true
namespace Minimal180.PairRepair
open Finset SimpleGraph Graffiti177 Graffiti318 Rooted180 Converse180 Assembly180 Substitution Transversals
open Classical
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

def TransPair (G : SimpleGraph V) (a b : V) : Prop := a≠b ∧ TwoColor G (univ\{a,b})

def SoloPossible (G : SimpleGraph V) (a b : V) : Prop :=
  G.degree a=4 ∧ ∀ c : V→Bool,ProperOn G (univ\{a,b}) c → ∀ i,(sideNeighbors G a c i).card=2

noncomputable def PairBudget (G : SimpleGraph V) (a b : V) := max 2 (max (G.degree a-2) (G.degree b-2))

def BothPossible (G : SimpleGraph V) (a b : V) : Prop :=
  ∀ c : V→Bool,ProperOn G (univ\{a,b}) c → ∀ i j,
    PairBudget G a b < (sideNeighbors G a c i∪sideNeighbors G b c j).card

/-- A single set must satisfy the binary constraints for all transversal
pairs simultaneously. The constraints only use the graph. They are
necessary for a failed marking, with no claim of sufficiency. -/
def PairCover (G : SimpleGraph V) (K : Finset V) : Prop :=
  Indep G K ∧ ∀ a b,TransPair G a b →
    (a∈K ∨ b∈K) ∧ (b∉K → SoloPossible G a b) ∧ (a∈K → b∈K → BothPossible G a b)

theorem failed_cover (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    (r : V) (p : Bool) (A : Finset V) (ai : Indep G A) (bad : ¬Protected G r p A) :
    PairCover G (A∩insert r (parity G r p)) := by
  let K := A∩insert r (parity G r p)
  refine ⟨fun x xm y ym => ai x (mem_inter.mp xm).1 y (mem_inter.mp ym).1,?_⟩
  intro a b pair
  obtain ⟨ab,bi⟩ := pair
  have hit : a∈K ∨ b∈K := by
    rcases (pair_obstruction G gc hn r p A ai bad a b ab bi).2 with h|h|h
    · exact Or.inl h.1
    · exact Or.inr h.1
    · exact Or.inl h.1
  refine ⟨hit,fun bk => ?_,fun ak bk c cp i j => ?_⟩
  · have rig := solo_rigidity G gc hn r p A ai bad a b ab bi (hit.resolve_right bk) bk
    exact ⟨rig.1,rig.2.2⟩
  · obtain ⟨two,high⟩ := budget_two G gc hn r p A ai bad a b ab bi
    have la := protected_degree G gc high r a p A ai ak
    have lb := protected_degree G gc high r b p A ai bk
    exact (max_le two (max_le la lb)).trans_lt (double_rigidity G gc hn r p A ai bad a b ab ak bk c cp i j)

theorem of_no_cover (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    (no : ∀ K,¬PairCover G K) (r : V) (p : Bool) (A : Finset V) (ai : Indep G A) : Protected G r p A := by
  by_contra bad;exact no _ (failed_cover G gc hn r p A ai bad)

theorem partner_forced (G : SimpleGraph V) {K : Finset V} (cover : PairCover G K)
    {a b : V} (pair : TransPair G a b) (excluded : ¬SoloPossible G a b) : b∈K := by
  by_contra bk;exact excluded ((cover.2 a b pair).2.1 bk)

/-- Adjacent partners of one tip force that tip into any candidate cover. -/
theorem center_forced (G : SimpleGraph V) {K : Finset V} (cover : PairCover G K)
    {t u v : V} (tu : TransPair G t u) (tv : TransPair G t v) (uv : G.Adj u v) : t∈K := by
  by_contra tm
  exact cover.1 u ((cover.2 _ _ tu).1.resolve_left tm) v ((cover.2 _ _ tv).1.resolve_left tm) uv.ne uv

theorem two_forced_centers (G : SimpleGraph V) {a b x y z w : V}
    (ab : G.Adj a b) (ax : TransPair G a x) (ay : TransPair G a y) (xy : G.Adj x y)
    (bz : TransPair G b z) (bw : TransPair G b w) (zw : G.Adj z w) : ∀ K,¬PairCover G K := by
  intro K cover
  exact cover.1 a (center_forced G cover ax ay xy) b (center_forced G cover bz bw zw) ab.ne ab

theorem cover_substitutions {W : Type*} [Fintype W] [DecidableEq W] {H : SimpleGraph W}
    {G : SimpleGraph V} {f : W→V} (h : Bags H G f) (gc : G.Connected) (hn : 1<Fintype.card V)
    (no : ∀ K,¬PairCover G K) : (∀ r p A,Indep H A → Protected H r p A) ∧
      (∀ r,PrimeTests H r) ∧ 1+independence H+maxEven H≤maxLeaves H+bipartiteNum H := by
  have good (r : W) (p : Bool) (A : Finset W) (ai : Indep H A) :=
    substitution_protection h gc hn r p A ai (of_no_cover G gc hn no (f r) p (A.image f) (h.indSupport A ai))
  exact ⟨good,fun r => protected_tests H r (good r),protected_ordinary H (h.connected gc hn) good⟩

theorem universal_iff_cover_remainder : Assembly180.Universal.{u} ↔
    ∀ (W : Type u) [Fintype W] [DecidableEq W] (G : SimpleGraph W),G.Connected →
      2<Fintype.card W → Prime G → bipartiteNum G+1<Fintype.card W → (∀ a b,¬GoodPair G a b) →
      (∃ K,PairCover G K) → ∀ r,(∀ y,¬DomEdge G r y) → PrimeTests G r := by
  constructor
  · intro all W _ _ G gc hi _ _ _ _ r no;exact universal_prime_tests all G gc hi r no
  · intro test
    apply universal_iff_remaining_tests.mpr
    intro W _ _ G gc hi prime rank pair r no
    by_cases some : ∃ K,PairCover G K
    · exact test W G gc hi prime rank pair some r no
    · exact protected_tests G r (of_no_cover G gc (by omega) (fun K k => some ⟨K,k⟩) r)

#print axioms failed_cover
#print axioms center_forced
#print axioms two_forced_centers
#print axioms cover_substitutions
#print axioms universal_iff_cover_remainder
end Minimal180.PairRepair
