import PrimeTests180
import LowMark180
import Mathlib.Tactic.Ring

set_option warningAsError true
namespace Minimal180.Substitution
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 PortParity
open Classical
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The ordinary counterexample from a failed odd root test on G has
order at most 4(n+1)(d+2)-1, where d counts odd marked vertices. -/
theorem realize_odd_failure (G : SimpleGraph V) (gc : G.Connected) (high : 2<Fintype.card V)
    (r : V) (no : ∀ y,¬DomEdge G r y) (I : Finset V) (ii : Indep G I) (ir : r∈I)
    (bad : ¬OddRootTest G r I) :
    counterexampleAtMost.{u} (4*(Fintype.card V+1)*((I∩parity G r true).card+2)-1) := by
  classical
  have nh (i : V) : ¬Universal G i := by
    intro hub
    have idB : Bags G G id := ⟨Function.surjective_id,fun _ => Iff.rfl⟩
    obtain ⟨y,ed⟩ := idB.hubEdge gc (by omega) hub r
    exact no y ed
  let h := twinChart G r
  let H := ear G (twinPorts G r true)
  let a : V⊕Unit := .inr ()
  let A := I.image (Sum.inl : V→V⊕Unit)
  let Q := parity G r true
  let P := parity H a true
  let D := A∩P
  have dc : D=(insert r (I∩Q)).image Sum.inl := (h.marks gc (by omega) I ir).2.2.2
  have off : r∉I∩Q := by simp [Q,mem_parity,dist_self]
  have size : D.card=(I∩Q).card+1 := by rw [dc,card_image_of_injective _ Sum.inl_injective,card_insert_of_not_mem off]
  have n : Fintype.card (V⊕Unit)=Fintype.card V+1 := by simp
  have upper := realize_pinned_failure H (h.bags.connected gc (by omega)) (by omega) a true A D
    (h.ind_image ii) Subset.rfl (fun yes => bad ((h.odd_iff gc high nh I ir).mp yes))
  rw [n,size] at upper
  convert upper using 2
  dsimp only [Q]
  ring

theorem bipartite_prime_tests (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    (bi : TwoColor G univ) (r : V) : PrimeTests G r := by
  constructor
  · intro p A ai
    have ok := weighted_order G gc hn r p.toNat A ai
    refine ⟨univ,bi,subset_univ _,?_⟩
    change A.card+(parity G r p).card+1≤Fintype.card V+weightedLeaves G (eligible A (parity G r p) r) at ok
    rw [card_univ]; omega
  · intro I ii _
    have ok := weighted_order G gc hn r true.toNat I ii
    refine ⟨univ,bi,subset_univ _,?_⟩
    change I.card+(parity G r true).card+1≤Fintype.card V+weightedLeaves G (eligible I (parity G r true) r) at ok
    rw [card_univ]; omega

theorem subcubic_prime_tests (G : SimpleGraph V) (r : V) (low : ∀ v,G.degree v≤3)
    (rooted : ∀ p,localBound G r (parity G r p)) : PrimeTests G r :=
  ⟨fun p A ai => pinned_of_low_marks G r p A ai (fun x _ => low x) (rooted p),
   fun I ii ir => odd_of_low_marks G r I ii ir (fun x _ => low x) (rooted true)⟩

/-- Exact universal reduction with bipartite prime graphs removed. -/
theorem universal_iff_nonbipartite_prime_tests : Assembly180.Universal.{u} ↔
    ∀ (W : Type u) [Fintype W] [DecidableEq W] (G : SimpleGraph W),G.Connected →
      2<Fintype.card W → Prime G → ¬TwoColor G univ → ∀ r,(∀ y,¬DomEdge G r y) → PrimeTests G r := by
  constructor
  · intro all W _ _ G gc high _ _ r no
    exact universal_prime_tests all G gc high r no
  · intro tests
    apply universal_iff_prime_tests.mpr
    intro W _ _ G gc high prime r no
    by_cases bi : TwoColor G univ
    · exact bipartite_prime_tests G gc (by omega) bi r
    · exact tests W G gc high prime bi r no

#print axioms realize_odd_failure
#print axioms bipartite_prime_tests
#print axioms subcubic_prime_tests
#print axioms universal_iff_nonbipartite_prime_tests
end Minimal180.Substitution
