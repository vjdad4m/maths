import ConeRoute
namespace Graffiti199Depleted.Catalogue.Incomplete
open SimpleGraph Anchored
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {X M : Set V} {z r a b x : V}

omit [DecidableRel G.Adj] in
theorem SingletonCut.complement_of_cone (F : SingletonCut G X z r a b) (sub : M ⊆ X) (v : V) :
    v ∈ (insert r (X \ M))ᶜ ↔ v = z ∨ v = a ∨ v = b ∨ v ∈ M := by
  have zr := (F.cut.2 r).mpr (by simp)
  have aX := F.offX a (by simp)
  have bX := F.offX b (by simp)
  have rX := F.offX r (by simp)
  change ¬ (v = r ∨ v ∈ X ∧ v ∉ M) ↔ _
  constructor
  · intro off
    rcases F.cover v with vx|e|e|e|e
    · exact Or.inr (Or.inr (Or.inr (Classical.byContradiction fun vm => off (Or.inr ⟨vx,vm⟩))))
    · exact Or.inl e
    · exact (off (Or.inl e)).elim
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr (Or.inl e))
  · rintro (e|e|e|m) (vr|h)
    · exact zr.ne (e.symm.trans vr)
    · exact F.zX (e ▸ h.1)
    · exact F.ra (vr.symm.trans e)
    · exact aX (e ▸ h.1)
    · exact F.rb (vr.symm.trans e)
    · exact bX (e ▸ h.1)
    · exact rX (vr ▸ sub m)
    · exact h.2 m

/-- At arbitrary order in this singleton-cut branch, even one port
missing at most one ordinary vertex implies a Hamiltonian path. -/
theorem SingletonCut.traceable_of_one_almost_complete (F : SingletonCut G X z r a b)
    (P : PathOn G {v | v ≠ z}) (almost : ∀ v ∈ X, ¬ G.Adj r v → v = x) : Traceable G := by
  classical
  by_contra no
  obtain ⟨xX,_,xa,xb,_⟩ := F.unique_miss_degree_and_contacts no P almost
  obtain ⟨p,pX,xp,tip,_,_⟩ := F.single_miss_core no P almost
  let H := X \ ({x} : Set V)
  have sub : H ⊆ X := fun _ h => h.1
  have comp : ∀ v ∈ H, G.Adj r v := fun v hv => Classical.byContradiction fun miss => hv.2 (almost v hv.1 miss)
  have con : (G.induce H).Connected := connected_remove_pendant F.connX pX xp tip
  have four : P.terminalQuartet.card = 4 := by rw [P.terminalQuartet_card no,F.cubic]
  have room : 2 ≤ Nat.card H := room_of_quartet P.terminalQuartet {x} four (by simp) (by
    intro v hv
    by_cases vx : v = x
    · exact Or.inr (by simp [vx])
    · exact Or.inl ⟨F.flanks_in_shore no P v hv,vx⟩)
  have za := (F.cut.2 a).mpr (by simp)
  have zb := (F.cut.2 b).mpr (by simp)
  have zx : z ≠ x := fun e => F.zX (e.symm ▸ xX)
  let L := [z,a,x,b]
  let Q : PathOn G (insert r H)ᶜ := ⟨L,by simp [L],by simp [L,List.chain'_cons,za,xa.symm,xb],
    by simp [L,za.ne,zx,zb.ne,xa.ne.symm,F.ab,xb.ne],by
      intro v
      rw [F.complement_of_cone (Set.singleton_subset_iff.mpr xX)]
      simp [L,or_left_comm,or_comm]⟩
  -- Use the explicit ends of the four-vertex cycle when opening it.
  exact no (F.traceable_of_neighbor_part_cycle sub comp con room Q (show G.Adj b z from zb.symm))

#print axioms SingletonCut.traceable_of_one_almost_complete
end Graffiti199Depleted.Catalogue.Incomplete
