import FlankAttachment

open private traceable_of_omission_permutation from OmissionSplice

namespace Graffiti199Depleted

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {z : V}

theorem traceable_of_joined_omission_endpoints [DecidableEq V]
    (p : PathOn G {v | v ≠ z}) {y : V} (zy : G.Adj z y) (edge : G.Adj p.last p.first) :
    Catalogue.Traceable G := by
  obtain ⟨A,R,split⟩ := List.append_of_mem ((p.covers y).mpr zy.ne.symm)
  let B := y :: R
  have old : (A ++ B).Chain' G.Adj := by simpa only [B,split] using p.chain
  have rotate : (B ++ A).Chain' G.Adj := by
    apply old.right_of_append.append old.left_of_append
    intro u hu v hv
    have uIs : u = p.last := by
      have mem := List.mem_getLast?_append_of_mem_getLast? (l₁ := A) hu
      have eq : (A ++ B).getLast? = some p.last := by
        rw [← show p.vertices = A ++ B from split]
        exact List.getLast?_eq_getLast p.nonempty
      rw [eq] at mem
      exact (Option.mem_some_iff.mp mem).symm
    have vIs : v = p.first := by
      have mem := List.mem_head?_append_of_mem_head? (t := B) hv
      have eq : (A ++ B).head? = some p.first := by
        rw [← show p.vertices = A ++ B from split]
        exact List.head?_eq_head p.nonempty
      rw [eq] at mem
      exact (Option.mem_some_iff.mp mem).symm
    exact uIs.symm ▸ vIs.symm ▸ edge
  have chain : (z :: (B ++ A)).Chain' G.Adj := by
    apply rotate.cons'
    intro v hv
    have e : y = v := by simpa [B] using hv
    exact e ▸ zy
  have perm : (z :: (B ++ A)).Perm (z :: p.vertices) := by
    rw [show p.vertices = A ++ B from split]
    exact (List.perm_append_comm (l₁ := B) (l₂ := A)).cons _
  exact traceable_of_omission_permutation p perm chain

namespace PathOn

variable [DecidableRel G.Adj] [DecidableEq V] [Fintype V]
variable (p : PathOn G {v | v ≠ z})

/-- In the no-independent-six branch, the initial vertex must equal
or see a predecessor of an omitted neighbor. That predecessor
cannot simultaneously be a successor of an omitted neighbor. -/
theorem initial_reaches_exclusive_predecessor (noTrace : ¬ Catalogue.Traceable G)
    (noSix : NoIndependentSix G) (deg : G.degree z = 3) :
    ∃ x ∈ p.predecessors, x ∉ p.rev.predecessors ∧ (x = p.first ∨ G.Adj p.first x) := by
  classical
  have positive : 0 < (G.neighborFinset z).card := by
    rw [G.card_neighborFinset_eq_degree,deg]
    decide
  obtain ⟨y,yMem⟩ := Finset.card_pos.mp positive
  have zy := (G.mem_neighborFinset _ _).mp yMem
  have noJoin : ¬ G.Adj p.last p.first := fun e =>
    noTrace (traceable_of_joined_omission_endpoints p zy e)
  have distinct : p.first ≠ p.last := by
    intro e
    obtain ⟨i,_⟩ := p.neighbor_has_position noTrace zy
    have il := i.isLt
    have first : p.first = p.vertices[0]'(by omega) := List.head_eq_getElem p.nonempty
    have last : p.last = p.vertices[p.vertices.length-1]'(by omega) := List.getLast_eq_getElem p.nonempty
    rw [first,last] at e
    have clash : 0 = p.vertices.length - 1 := p.nodup.getElem_inj_iff.mp e
    omega
  have notZ : p.first ≠ z := (p.covers p.first).mp (List.head_mem p.nonempty)
  have restrictAsStart (x : V) (how : x = p.first ∨ G.Adj p.first x) :
      x ∉ p.rev.predecessors := by
    intro h
    obtain ⟨i,adj,eq⟩ := p.rev.mem_predecessors.mp h
    rcases how with rfl|edge
    · exact p.rev.before_ne_last i (eq.trans p.rev_last.symm)
    · have e : G.Adj p.rev.last (p.rev.before i) := p.rev_last.symm ▸ eq.symm ▸ edge
      exact p.rev.terminal_not_adj_predecessor noTrace i adj e
  by_cases sP : p.first ∈ p.predecessors
  · exact ⟨p.first,sP,restrictAsStart _ (Or.inl rfl),Or.inl rfl⟩
  · let I := insert z p.terminalFlanks
    have main := p.omitted_and_terminalFlanks_independent noTrace
    have five : I.card = 5 := main.1.trans (by rw [deg])
    have sOff : p.first ∉ I := by
      simp [I,terminalFlanks,notZ,distinct,sP]
    have six : (insert p.first I).card = 6 :=
      (Finset.card_insert_of_not_mem sOff).trans (by rw [five])
    obtain ⟨a,ha,b,hb,edge⟩ := noSix (insert p.first I) six
    have other (v : V) (vI : v ∈ I) (e : G.Adj p.first v) :
        ∃ x ∈ p.predecessors, x ∉ p.rev.predecessors ∧ (x = p.first ∨ G.Adj p.first x) := by
      rcases Finset.mem_insert.mp vI with rfl|w
      · exact ((omission_constraints noTrace p).firstOff e.symm).elim
      · rcases Finset.mem_insert.mp w with rfl|pre
        · exact (noJoin e.symm).elim
        · exact ⟨v,pre,restrictAsStart _ (Or.inr e),Or.inr e⟩
    rcases Finset.mem_insert.mp ha with rfl|aI <;> rcases Finset.mem_insert.mp hb with rfl|bI
    · exact (G.loopless _ edge).elim
    · exact other b bI edge
    · exact other a aI edge.symm
    · exact (main.2 a aI b bI edge).elim

end PathOn

#print axioms PathOn.initial_reaches_exclusive_predecessor

end Graffiti199Depleted
