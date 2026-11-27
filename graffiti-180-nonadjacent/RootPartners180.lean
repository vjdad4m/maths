import RootPairRepair180
import SharedBudget180
import SaturatedLayer180

set_option warningAsError true
namespace Minimal180.PairRepair
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 Substitution Transversals
open Classical
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Every transversal partner of the root must be protected under the
same failed marking. This also applies when the root itself is unprotected. -/
theorem root_partner (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    (r : V) (p : Bool) (A : Finset V) (ai : Indep G A) (bad : ¬Protected G r p A)
    {b : V} (pair : TransPair G r b) : b∈A∩insert r (parity G r p) := by
  have cov := failed_cover G gc hn r p A ai bad
  by_contra miss
  have rk := (cov.2 r b pair).1.resolve_right miss
  have na := (pair_obstruction G gc hn r p A ai bad r b pair.1 pair.2).1
  exact bad (root_solo_protected G gc hn r b pair.1 na pair.2 p A ai rk miss)

theorem adjacent_root_partners (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    {r b c : V} (pb : TransPair G r b) (pc : TransPair G r c) (bc : G.Adj b c) : PrimeTests G r := by
  apply protected_tests
  intro p A ai
  by_contra bad
  have bm := root_partner G gc hn r p A ai bad pb
  have cm := root_partner G gc hn r p A ai bad pc
  exact ai b (mem_inter.mp bm).1 c (mem_inter.mp cm).1 bc.ne bc

theorem mixed_parity_partners (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    {r b c : V} (pb : TransPair G r b) (pc : TransPair G r c)
    (diff : G.dist b r%2≠G.dist c r%2) : PrimeTests G r := by
  apply protected_tests
  intro p A ai
  by_contra bad
  have bm := root_partner G gc hn r p A ai bad pb
  have cm := root_partner G gc hn r p A ai bad pc
  have be := (mem_parity G r b p).mp ((mem_insert.mp (mem_inter.mp bm).2).resolve_left pb.1.symm)
  have ce := (mem_parity G r c p).mp ((mem_insert.mp (mem_inter.mp cm).2).resolve_left pc.1.symm)
  exact diff (be.trans ce.symm)


/-- Two tips in a common root layer cannot have exactly one protected.
The same-layer description of a degree-four solo tip would make them adjacent. -/
theorem equal_layer_pair (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    (r : V) (p : Bool) (A : Finset V) (ai : Indep G A) (bad : ¬Protected G r p A)
    {a b : V} (pair : TransPair G a b) (dist : G.dist a r=G.dist b r) :
    a∈A∩insert r (parity G r p) ∧ b∈A∩insert r (parity G r p) := by
  let K := A∩insert r (parity G r p)
  have cov := failed_cover G gc hn r p A ai bad
  have force {x y : V} (h : TransPair G x y) (same : G.dist y r=G.dist x r) : y∈K := by
    by_contra miss
    have xm := (cov.2 x y h).1.resolve_right miss
    by_cases eq : x=r
    · subst x;exact miss (root_partner G gc hn r p A ai bad h)
    have px := (mem_insert.mp (mem_inter.mp xm).2).resolve_left eq
    have py : y∈parity G r p := (mem_parity G r y p).mpr (same ▸ (mem_parity G r x p).mp px)
    have out : y∉A := fun ya => miss (mem_inter.mpr ⟨ya,mem_insert_of_mem py⟩)
    have edge := (solo_layer G gc hn r p A ai bad x y h.1 h.2 xm miss eq y same).mp out
    exact (pair_obstruction G gc hn r p A ai bad x y h.1 h.2).1 edge
  exact ⟨force ⟨pair.1.symm,by simpa only [pair_comm b a] using pair.2⟩ dist,force pair dist.symm⟩

/-- Any transversal pair lying in one layer settles every marking for the
other distance parity at this root. -/
theorem opposite_layer_protected (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    (r : V) (p : Bool) (A : Finset V) (ai : Indep G A) {a b : V} (pair : TransPair G a b)
    (same : G.dist a r=G.dist b r) (out : a∉parity G r p) : Protected G r p A := by
  by_contra bad
  have ⟨ak,bk⟩ := equal_layer_pair G gc hn r p A ai bad pair same
  have ar := (mem_insert.mp (mem_inter.mp ak).2).resolve_right out
  have bo : b∉parity G r p := fun bm => out ((mem_parity G r a p).mpr
    (same ▸ (mem_parity G r b p).mp bm))
  have br := (mem_insert.mp (mem_inter.mp bk).2).resolve_right bo
  exact pair.1 (ar.trans br.symm)

def RootCover (G : SimpleGraph V) (r : V) (p : Bool) (K : Finset V) : Prop :=
  SharedCover G K ∧ K⊆insert r (parity G r p) ∧ (∀ b,TransPair G r b → b∈K) ∧
    ∀ a b,TransPair G a b → G.dist a r=G.dist b r → a∈K ∧ b∈K

theorem root_cover_failure (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    (r : V) (p : Bool) (A : Finset V) (ai : Indep G A) (bad : ¬Protected G r p A) :
    RootCover G r p (A∩insert r (parity G r p)) :=
  ⟨shared_failure G gc hn r p A ai bad,inter_subset_right,(fun _ h => root_partner G gc hn r p A ai bad h),
    fun _ _ h d => equal_layer_pair G gc hn r p A ai bad h d⟩

theorem universal_iff_root_partners : Assembly180.Universal.{u} ↔
    ∀ (W : Type u) [Fintype W] [DecidableEq W] (G : SimpleGraph W),G.Connected →
      2<Fintype.card W → Prime G → bipartiteNum G+1<Fintype.card W → (∀ a b,¬GoodPair G a b) →
      ∀ r,(∀ y,¬DomEdge G r y) → (∃ p K,RootCover G r p K) → PrimeTests G r := by
  constructor
  · intro all W _ _ G gc high _ _ _ r no _;exact universal_prime_tests all G gc high r no
  · intro test
    apply universal_iff_remaining_tests.mpr
    intro W _ _ G gc high prime rank pair r no
    by_cases yes : ∃ p K,RootCover G r p K
    · exact test W G gc high prime rank pair r no yes
    · apply protected_tests
      intro p A ai
      by_contra bad
      exact yes ⟨p,_,root_cover_failure G gc (by omega) r p A ai bad⟩

#print axioms opposite_layer_protected
#print axioms equal_layer_pair
#print axioms root_partner
#print axioms adjacent_root_partners
#print axioms mixed_parity_partners
#print axioms root_cover_failure
#print axioms universal_iff_root_partners
end Minimal180.PairRepair
