import CompressedRoute
import PendantExterior
open private six_le_treeNumber_of_five_independent_neighbors from CubicEdgeCuts
open private open_at from ConnectedAlphaTwo
namespace Graffiti199Depleted.Catalogue.Incomplete
open SimpleGraph Anchored
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V]
variable {X H : Set V} {z r a b : V}

/-- An independent set in a port and a collection of its ordinary neighbors has
size at most three. The singleton is the additional independent neighbor. -/
theorem SingletonCut.cone_cap (F : SingletonCut G X z r a b) (sub : H ⊆ X)
    (on : ∀ v ∈ H, G.Adj r v) (T : Finset V) (inside : ∀ t ∈ T, t ∈ insert r H)
    (stable : ∀ u ∈ T, ∀ v ∈ T, ¬ G.Adj u v) : T.card ≤ 3 := by
  classical
  by_cases rt : r ∈ T
  · have one : T ⊆ {r} := by
      intro u hu
      rcases inside u hu with eq|h
      · simpa using eq
      · exact (stable r rt u hu (on u h)).elim
    have bound := Finset.card_le_card one
    rw [Finset.card_singleton] at bound; omega
  have ht (u : V) (hu : u ∈ T) : u ∈ H := (inside u hu).resolve_left (fun eq => rt (eq ▸ hu))
  have zt : z ∉ T := fun h => F.zX (sub (ht z h))
  by_contra bad
  have cnt := Finset.card_insert_of_not_mem zt
  apply Nat.not_succ_le_self 5
  apply Nat.le_trans (six_le_treeNumber_of_five_independent_neighbors (insert z T) r (by omega) ?_ ?_) F.budget
  · intro u hu
    rcases Finset.mem_insert.mp hu with rfl|h
    · exact ((F.cut.2 r).mpr (by simp)).symm
    · exact on _ (ht _ h)
  · intro u hu v hv
    rcases Finset.mem_insert.mp hu with rfl|um <;> rcases Finset.mem_insert.mp hv with rfl|vm
    · exact G.loopless _
    · exact fun e => F.offX _ ((F.cut.2 _).mp e) (sub (ht _ vm))
    · exact fun e => F.offX _ ((F.cut.2 _).mp e.symm) (sub (ht _ um))
    · exact stable u um v vm

/-- Contract the complement of an ordinary neighbor set together with its port.
A spanning cycle on the discarded vertices supplies every possible exit. -/
theorem SingletonCut.traceable_of_neighbor_part_cycle (F : SingletonCut G X z r a b)
    (sub : H ⊆ X) (on : ∀ v ∈ H, G.Adj r v) (hc : (G.induce H).Connected)
    (room : 2 ≤ Nat.card H)
    (Q : PathOn G (insert r H)ᶜ) (close : G.Adj Q.last Q.first) : Traceable G := by
  classical
  let W := insert r H
  have off : r ∉ H := fun hr => F.offX r (by simp) (sub hr)
  have cardinal : 2 < Fintype.card W := by
    have eq : W.toFinset = insert r H.toFinset := Set.toFinset_insert
    have zr : r ∉ H.toFinset := by simpa using off
    have c := congrArg Finset.card eq
    rw [Finset.card_insert_of_not_mem zr,Set.toFinset_card,Set.toFinset_card] at c
    rw [Nat.card_eq_fintype_card] at room; omega
  have two := two_of_universal_vertex hc off on cardinal
  have zo : z ∉ W := by
    rintro (zr|zh)
    · exact F.cut.1 (by simp [zr])
    · exact F.zX (sub zh)
  apply traceable_via_exterior (W := W) F.conn two zo (F.cone_cap sub on)
  intro t ht _
  obtain ⟨s,L⟩ := open_at Q (Or.inr close) ht
  exact ⟨s,L.reverse⟩

/-- Deleting at most two named ordinary vertices from a shore containing
an independent predecessor quartet leaves at least two vertices. -/
theorem room_of_quartet (T R : Finset V) (four : T.card = 4) (few : R.card ≤ 2)
    (inside : ∀ t ∈ T, t ∈ H ∨ t ∈ R) : 2 ≤ Nat.card H := by
  classical
  have sub : T ⊆ H.toFinset ∪ R := by
    intro t ht
    simpa only [Finset.mem_union,Set.mem_toFinset] using inside t ht
  have lo := Finset.card_le_card sub
  have hi := Finset.card_union_le H.toFinset R
  have c : Nat.card H = H.toFinset.card := Nat.card_eq_fintype_card.trans (Set.toFinset_card H).symm
  rw [c]; omega

#print axioms SingletonCut.traceable_of_neighbor_part_cycle
end Graffiti199Depleted.Catalogue.Incomplete


