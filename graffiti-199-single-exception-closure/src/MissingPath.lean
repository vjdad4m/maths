import SingleException
open private open_at from ConnectedAlphaTwo
namespace Graffiti199Depleted.Catalogue.Incomplete
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] {X H M : Set V} {z r a b : V}

theorem SingletonCut.traceable_of_neighbor_path (F : SingletonCut G X z r a b)
    (sub : H ⊆ X) (on : ∀ v ∈ H, G.Adj r v) (P : PathOn G H)
    (Q : PathOn G (insert r H)ᶜ) (close : G.Adj Q.last Q.first) : Traceable G := by
  have zr := (F.cut.2 r).mpr (by simp)
  have rH : r ∉ H := fun h => F.offX r (by simp) (sub h)
  have zW : z ∈ (insert r H)ᶜ := by rintro (e|h); exact zr.ne e; exact F.zX (sub h)
  obtain ⟨s,L⟩ := open_at Q (Or.inr close) zW
  have pstart := (P.covers P.first).mp (List.head_mem P.nonempty)
  have tail := (Traverses.single r).join (show Traverses G H P.first P.last from ⟨P,rfl,rfl⟩)
    (Set.disjoint_singleton_left.mpr rH) (on _ pstart)
  have seq : Traverses G (insert r H) r P.last := by simpa using tail
  obtain ⟨T,_,_⟩ := L.reverse.join seq disjoint_compl_left zr
  have eq : (insert r H)ᶜ ∪ insert r H = Set.univ := Set.compl_union_self _
  exact traceable_iff_hamiltonian_walk.mpr (pathOn_univ_iff_hamiltonian_walk.mp ⟨eq ▸ T⟩)

theorem SingletonCut.traceable_of_connected_neighbors (F : SingletonCut G X z r a b)
    (sub : H ⊆ X) (on : ∀ v ∈ H, G.Adj r v) (hc : (G.induce H).Connected)
    (Q : PathOn G (insert r H)ᶜ) (close : G.Adj Q.last Q.first) : Traceable G := by
  classical
  by_cases room : 2 ≤ Nat.card H
  · exact F.traceable_of_neighbor_part_cycle sub on hc room Q close
  obtain ⟨h⟩ := hc.nonempty
  have low : Nat.card H ≤ 1 := by omega
  haveI : Subsingleton H := Fintype.card_le_one_iff_subsingleton.mp (by simpa only [Nat.card_eq_fintype_card] using low)
  have eq : H = {h.val} := by
    ext v; exact ⟨fun hv => congrArg Subtype.val (Subsingleton.elim (⟨v,hv⟩ : H) h),
      fun e => (show v = h.val from e).symm ▸ h.property⟩
  obtain ⟨P,_,_⟩ := Traverses.single (G := G) h.val
  exact F.traceable_of_neighbor_path sub on (eq.symm ▸ P) Q close

/-- An a-to-b spanning route through the ordinary nonneighbors closes
a cycle with the singleton. Its endpoints may coincide for a one-vertex path. -/
theorem SingletonCut.cycle_from_missing_path (F : SingletonCut G X z r a b)
    (sub : M ⊆ X) {u v : V} (P : Traverses G M u v) (start : G.Adj a u) (finish : G.Adj b v) :
    ∃ Q : PathOn G (insert r (X \ M))ᶜ, G.Adj Q.last Q.first := by
  classical
  have za := (F.cut.2 a).mpr (by simp)
  have zb := (F.cut.2 b).mpr (by simp)
  have aM : a ∉ M := fun h => F.offX a (by simp) (sub h)
  have bM : b ∉ M := fun h => F.offX b (by simp) (sub h)
  have zM : z ∉ M := fun h => F.zX (sub h)
  have L := (Traverses.single z).join (Traverses.single a) (by simpa using za.ne) za
  have A := L.join P (by simp [Set.disjoint_union_left,zM,aM]) start
  have B := A.join (Traverses.single b) (by simp [Set.disjoint_union_left,zb.ne.symm,F.ab.symm,bM]) finish.symm
  have eq : ((({z} : Set V) ∪ {a}) ∪ M) ∪ {b} = (insert r (X \ M))ᶜ := by
    ext t; rw [F.complement_of_cone sub]; simp only [Set.mem_union,Set.mem_singleton_iff]; tauto
  obtain ⟨Q,h0,h1⟩ := eq ▸ B
  exact ⟨Q,h1.symm ▸ h0.symm ▸ zb.symm⟩

/-- Applies to arbitrarily many ordinary nonneighbors, including a cut in
which every port has at least two nonneighbors. -/
theorem SingletonCut.traceable_of_routable_nonneighbors (F : SingletonCut G X z r a b)
    (sub : M ⊆ X) (on : ∀ v ∈ X \ M, G.Adj r v) (hc : (G.induce (X \ M)).Connected)
    {u v : V} (P : Traverses G M u v) (start : G.Adj a u) (finish : G.Adj b v) : Traceable G := by
  obtain ⟨Q,close⟩ := F.cycle_from_missing_path sub P start finish
  exact F.traceable_of_connected_neighbors (fun _ h => h.1) on hc Q close

#print axioms SingletonCut.traceable_of_routable_nonneighbors
end Graffiti199Depleted.Catalogue.Incomplete

