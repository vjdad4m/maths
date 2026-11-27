import ForceMarks180
import PrimeCubic180

set_option warningAsError true
namespace Minimal180.Substitution
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
open Classical
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The bipartite witness must contain every designated doubly marked
vertex. Its order is the order actually used on the right hand side. -/
def Pinned (G : SimpleGraph V) (r : V) (p : Bool) (A D : Finset V) : Prop :=
  ∃ Z,TwoColor G Z ∧ D⊆Z ∧
    1+A.card+(parity G r p).card≤weightedLeaves G (eligible A (parity G r p) r)+Z.card

theorem realize_pinned_failure (G : SimpleGraph V) (gc : G.Connected) (hn : 2<Fintype.card V)
    (r : V) (p : Bool) (A D : Finset V) (ai : Indep G A) (both : D⊆A∩parity G r p)
    (bad : ¬Pinned G r p A D) :
    counterexampleAtMost.{u} (4*(Fintype.card V+D.card*Fintype.card V)-1) := by
  classical
  have fail : ¬localBound (force G D) (.inl r) (parity (force G D) (.inl r) p) :=
    fun up => bad (forced_witness G gc hn A D ai r p both up)
  have h := force_bags G D
  have size : Fintype.card (Forced D)=Fintype.card V+D.card*Fintype.card V := by
    simp [Forced,Copies,Fintype.card_prod,Fintype.card_sum]
  have witness := of_failed_local (force G D) (h.connected gc (by omega)) (by omega) _ _ fail
  rwa [size] at witness

/-- The existing universal ordinary statement implies the pinned test
on every connected graph of order at least three, including base graphs
on which the unpinned test has already been proved. -/
theorem universal_pins (all : Assembly180.Universal.{u}) (G : SimpleGraph V) (gc : G.Connected)
    (hn : 2<Fintype.card V) (r : V) (p : Bool) (A D : Finset V) (ai : Indep G A)
    (both : D⊆A∩parity G r p) : Pinned G r p A D := by
  by_contra no
  obtain ⟨W,ft,de,J,jc,jn,_,bad⟩ := realize_pinned_failure G gc hn r p A D ai both no
  letI := ft
  letI := de
  exact (Nat.not_lt_of_ge (all W J jc jn)) bad

/-- The unrestricted ordinary conjecture is equivalent to a pinned
bipartite-witness statement on biconnected blocks. Only roots incident
to no dominating edge have to be tested. -/
theorem universal_iff_pinned_blocks : Assembly180.Universal.{u} ↔
    ∀ (W : Type u) [Fintype W] [DecidableEq W] (G : SimpleGraph W),G.Connected →
      2<Fintype.card W → NoCut G → ∀ r,(∀ y,¬DomEdge G r y) → ∀ p A,Indep G A →
        Pinned G r p A (A∩parity G r p) := by
  constructor
  · intro all W _ _ G gc hn _ r _ p A ai
    exact universal_pins all G gc hn r p A _ ai Subset.rfl
  · intro tests
    apply Assembly180.universal_iff_blocks.mpr
    intro W _ _ G gc hn nc r p
    by_cases hit : ∃ y,DomEdge G r y
    · obtain ⟨_,e⟩ := hit
      exact dom_edge_rooted G gc hn e p
    have none : ∀ y,¬DomEdge G r y := by simpa using hit
    have nh (c : W) : ¬Universal G c := by
      intro u
      have idB : Bags G G id := ⟨Function.surjective_id,fun _ => Iff.rfl⟩
      exact hit (idB.hubEdge gc hn u r)
    have large := three_of_nohub G gc hn nh
    intro A ai
    obtain ⟨Z,col,_,ok⟩ := tests W G gc large nc r none p A ai
    exact ok.trans (Nat.add_le_add_left (size_bip G col) _)

#print axioms realize_pinned_failure
#print axioms universal_pins
#print axioms universal_iff_pinned_blocks
end Minimal180.Substitution
