import DegreeFiveEightTerminalLift189
import TerminalOreClosure189

namespace Graffiti189EightTerminal
open SimpleGraph SimpleGraph.Walk Finset Graffiti189LongestPath.CrossSaturation
variable {V : Type*} {J : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel J.Adj]
set_option linter.unusedSectionVars false

/-- Complete only edges with a nonport endpoint, then preserve the exact
opposite-color endpoints on pulling the path back through Ore closure. -/
theorem terminal_walk_at_eight (e : Fin 8 ≃ V)
    (portHigh : ∀ i : Fin 8, i.val < 5 → 4 ≤ J.degree (e i))
    (nonHigh : ∀ i : Fin 8, 5 ≤ i.val → 5 ≤ J.degree (e i)) :
    ∃ u v : Fin 8, u.val < 2 ∧ 2 ≤ v.val ∧ v.val < 5 ∧
      ∃ p : J.Walk (e u) (e v), p.IsPath ∧ ∀ z, z ∈ p.support := by
  classical
  let H : SimpleGraph V :=
    ⟨fun x y => J.Adj x y ∨ (x ≠ y ∧ (5 ≤ (e.symm x).val ∨ 5 ≤ (e.symm y).val)),
      by intro x y; rintro (h|⟨h,k⟩); exact .inl h.symm; exact .inr ⟨h.symm,k.symm⟩,
      by intro x; rintro (h|⟨h,_⟩); exact J.loopless _ h; exact h rfl⟩
  letI : DecidableRel H.Adj := Classical.decRel _
  have sub : J ≤ H := fun _ _ h => Or.inl h
  have high (v : V) : 4 ≤ J.degree v := by
    have ev : e (e.symm v) = v := e.apply_symm_apply _
    by_cases lo : (e.symm v).val < 5
    · have q := portHigh (e.symm v) lo
      rw [e.apply_symm_apply] at q
      exact q
    have q := nonHigh (e.symm v) (by omega)
    rw [ev] at q
    omega
  have cap (u v : V) (uv : H.Adj u v) (no : ¬ J.Adj u v) :
      Fintype.card V + 1 ≤ J.degree u + J.degree v := by
    have sz : Fintype.card V = 8 := by simpa using Fintype.card_congr e.symm
    change J.Adj u v ∨ _ at uv
    obtain ⟨_,q|q⟩ := uv.resolve_left no
    · have k := nonHigh (e.symm u) q
      rw [e.apply_symm_apply] at k
      have l := high v
      omega
    · have k := nonHigh (e.symm v) q
      rw [e.apply_symm_apply] at k
      have l := high u
      omega
  have original : ∃ i j : Fin 8, i.val < 5 ∧ j.val < 5 ∧ J.Adj (e i) (e j) := by
    apply Classical.byContradiction
    intro n
    have bind : J.neighborFinset (e 0) ⊆ ({e 5,e 6,e 7} : Finset V) := by
      intro v hv
      have h := (mem_neighborFinset J _ _).mp hv
      let z := e.symm v
      have ev : e z = v := e.apply_symm_apply _
      have h' : J.Adj (e 0) (e z) := ev.symm ▸ h
      have lo : 5 ≤ z.val := by
        by_cases l : 5 ≤ z.val
        · exact l
        exact (n ⟨0,z,by decide,by omega,h'⟩).elim
      have hex : z=5 ∨ z=6 ∨ z=7 := by
        have h := z.isLt
        have h' : z.val=5 ∨ z.val=6 ∨ z.val=7 := by omega
        rcases h' with h'|h'|h'
        · exact .inl (Fin.ext h')
        · exact .inr (.inl (Fin.ext h'))
        · exact .inr (.inr (Fin.ext h'))
      rcases hex with hz|hz|hz <;> rw [←ev,hz] <;> simp
    have q := (card_le_card bind).trans (card_insert_le _ _)
    have qr := card_insert_le (e 6) ({e 7} : Finset V)
    rw [card_singleton] at qr
    rw [card_neighborFinset_eq_degree] at q
    have p := portHigh 0 (by decide)
    omega
  obtain ⟨i,j,hi,hj,edge⟩ := original
  have ne : i ≠ j := fun eq => edge.ne (congrArg (fun w : Fin 8 => e w) eq)
  have fw (u v : Fin 8) (adj : allowed i j u v) : H.Adj (e u) (e v) := by
    obtain ⟨distinct,hu|hv|⟨hu,hv⟩|⟨hu,hv⟩⟩ := adj
    · exact .inr ⟨fun k=>distinct (e.injective k),.inl (by simpa using hu)⟩
    · exact .inr ⟨fun k=>distinct (e.injective k),.inr (by simpa using hv)⟩
    · exact .inl (by rw [hu,hv]; exact edge)
    · exact .inl (by rw [hu,hv]; exact edge.symm)
  obtain ⟨u,v,ul,vl,vu,p,pp,ps⟩ := walk_of_completed_route e i j hi hj ne fw
  exact ⟨u,v,ul,vl,vu,terminal_ore_closure sub cap p pp ps⟩

#print axioms terminal_walk_at_eight
end Graffiti189EightTerminal
