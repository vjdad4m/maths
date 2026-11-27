import MateFlank

namespace Graffiti199Depleted.PathOn

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {z : V}
variable [DecidableEq V] [DecidableRel G.Adj] [Fintype V]
variable (p : PathOn G {x | x ≠ z})

/-- A cubic neighbor k of a cubic omission has one successor-specific
alternative and one cross-contact alternative. The right endpoint
or a second neighbor intervenes within two steps of k, or the
predecessor of k sees another omitted neighbor. -/
theorem cubic_neighbor_position_constraint (noTrace : ¬ Catalogue.Traceable G)
    (budget : Catalogue.treeNumber G ≤ 5) {k a b : V}
    (kCubic : G.degree k = 3)
    (ka : k ≠ a) (kb : k ≠ b) (ab : a ≠ b)
    (zk : G.Adj z k) (za : G.Adj z a) (zb : G.Adj z b)
    (offKA : ¬ G.Adj k a) (offKB : ¬ G.Adj k b) (offAB : ¬ G.Adj a b)
    (i : p.EdgePosition) (ik : p.after i = k) :
    (i.val + 2 = p.vertices.length - 1) ∨
      (∃ j : p.EdgePosition, j.val = i.val + 2 ∧ G.Adj z (p.after j)) ∨
      G.Adj (p.before i) a ∨ G.Adj (p.before i) b := by
  have iLt := i.isLt
  have more : i.val + 2 < p.vertices.length := by
    by_contra! far
    have near : i.val + 1 = p.vertices.length - 1 := by omega
    have last : p.after i = p.last := by
      rw [PathOn.last,List.getLast_eq_getElem]
      simp only [after,near]
    exact (omission_constraints noTrace p).lastOff (last ▸ (ik.symm ▸ zk))
  let j : p.EdgePosition := ⟨i.val+1,by omega⟩
  have kj : p.before j = k := ik
  let c := p.before i
  let d := p.after j
  have cd : c ≠ d := by
    intro eq
    have clash : i.val = j.val + 1 := p.nodup.getElem_inj_iff.mp eq
    dsimp [j] at clash
    omega
  have cz : c ≠ z := (p.covers c).mp (p.before_mem i)
  have dz : d ≠ z := (p.covers d).mp (p.after_mem j)
  have kc : G.Adj k c := ik ▸ (p.before_adj_after i).symm
  have kd : G.Adj k d := kj ▸ p.before_adj_after j
  let D : Finset V := {z,c,d}
  have dCard : D.card = 3 := by
    have off : z ∉ ({c,d} : Finset V) := by simp [cz.symm,dz.symm]
    change (insert z ({c,d} : Finset V)).card = 3
    rw [Finset.card_insert_of_not_mem off,Finset.card_pair cd]
  have sub : D ⊆ G.neighborFinset k := by
    intro w hw
    apply (G.mem_neighborFinset _ _).mpr
    rcases (show w = z ∨ w = c ∨ w = d by simpa [D] using hw) with rfl|rfl|rfl
    · exact zk.symm
    · exact kc
    · exact kd
  have exactN : D = G.neighborFinset k := Finset.eq_of_subset_of_card_le sub (by
    rw [dCard,G.card_neighborFinset_eq_degree,kCubic])
  rcases p.predecessor_requires_other_contact noTrace budget ka kb ab zk za zb
      offKA offKB offAB i ik with share|aorb
  · obtain ⟨w,wW,wc,wk⟩ := share
    have wD : w ∈ D := exactN.symm ▸ (G.mem_neighborFinset _ _).mpr wk.symm
    have wz : w ≠ z := fun eq => p.omitted_off_terminalFlanks (eq ▸ wW)
    have wd : w = d := ((show w = z ∨ w = c ∨ w = d by simpa [D] using wD).resolve_left wz).resolve_left wc
    have dW : d ∈ p.terminalFlanks := wd ▸ wW
    rcases Finset.mem_insert.mp dW with last|pre
    · left
      rw [PathOn.last,List.getLast_eq_getElem] at last
      exact p.nodup.getElem_inj_iff.mp last
    · right
      left
      obtain ⟨r,rN,rd⟩ := p.mem_predecessors.mp pre
      have eq : r.val = j.val + 1 := p.nodup.getElem_inj_iff.mp rd
      exact ⟨r,eq,rN⟩
  · exact Or.inr (Or.inr aorb)

#print axioms cubic_neighbor_position_constraint

end Graffiti199Depleted.PathOn
