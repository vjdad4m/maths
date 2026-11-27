import Proof384b

namespace Graffiti384b
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Two adjacent vertices needing repair need not both be retained. -/
theorem pair_repair_saves (s : Finset V) (u v : V) (uv : G.Adj u v)
    (us : u ∉ s) (vs : v ∉ s) (one : nbr G u s = 1)
    (defv : nbr G v s < 2) :
    gamma G ≤ s.card + (univ.filter (fun x => x ∉ s ∧ nbr G x s < 2)).card - 1 := by
  classical
  let B := univ.filter (fun x => x ∉ s ∧ nbr G x s < 2)
  let R := B.erase u
  have uh : u ∈ B := mem_filter.mpr ⟨mem_univ _, us, by omega⟩
  have vh : v ∈ R := mem_erase.mpr ⟨uv.ne.symm, mem_filter.mpr ⟨mem_univ _, vs, defv⟩⟩
  have hh : TwoDominates G (s ∪ R) := by
    intro x hx
    have xs : x ∉ s := fun h => hx (mem_union_left _ h)
    by_cases hxu : x = u
    · subst x
      have e : ∃ w ∈ s.filter (G.Adj u), True := by
        have ne : (s.filter (G.Adj u)).Nonempty := card_pos.mp (by
          change 0 < nbr G u s
          omega)
        obtain ⟨w, hw⟩ := ne
        exact ⟨w, hw, trivial⟩
      obtain ⟨w,hw,_⟩ := e
      obtain ⟨ws, uw⟩ := mem_filter.mp hw
      have wv : w ≠ v := fun h => vs (h ▸ ws)
      have sub : ({w,v} : Finset V) ⊆ (s ∪ R).filter (G.Adj u) := by
        intro y hy
        rcases mem_insert.mp hy with rfl | h
        · exact mem_filter.mpr ⟨mem_union_left _ ws, uw⟩
        · rw [mem_singleton] at h
          subst y
          exact mem_filter.mpr ⟨mem_union_right _ vh, uv⟩
      exact (by simpa [nbr, wv] using card_le_card sub)
    · have enough : 2 ≤ nbr G x s := by
        by_contra! small
        exact hx (mem_union_right _ (show x ∈ R from
          mem_erase.mpr ⟨hxu,mem_filter.mpr ⟨mem_univ _, xs, small⟩⟩))
      exact enough.trans (card_le_card (filter_subset_filter _ (subset_union_left)))
  have bd : gamma G ≤ (s ∪ R).card := by
    exact Nat.sInf_le ⟨s ∪ R, hh, rfl⟩
  have c : R.card = B.card - 1 := card_erase_of_mem uh
  have mul := card_union_le s R
  have pos : 0 < B.card := card_pos.mpr ⟨u,uh⟩
  change gamma G ≤ s.card + B.card - 1
  omega

#print axioms pair_repair_saves
end Graffiti384b
