import DepletedFootprint

namespace Graffiti199Depleted

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

private theorem isolated_reachable_eq {x y : V}
    (isolated : ∀ v, ¬ G.Adj x v) (reach : G.Reachable x y) : x = y := by
  obtain ⟨p⟩ := reach
  cases p with
  | nil => rfl
  | cons e _ => exact (isolated _ e).elim

variable [Fintype V] [DecidableRel G.Adj]

/-- Connectivity after deleting fewer than three vertices guarantees
minimum degree at least three in a graph of order at least four. -/
theorem degree_of_small_deletion_preconnected
    (order : 4 ≤ Fintype.card V)
    (below : ∀ D : Finset V, D.card < 3 → (G.induce {v | v ∉ D}).Preconnected)
    (x : V) : 3 ≤ G.degree x := by
  classical
  by_contra small
  let D := G.neighborFinset x
  have count : D.card < 3 := by
    change (G.neighborFinset x).card < 3
    rw [G.card_neighborFinset_eq_degree]
    omega
  have xD : x ∉ D := G.not_mem_neighborFinset_self x
  have someOutside : (insert x D).card < (Finset.univ : Finset V).card := by
    rw [Finset.card_insert_of_not_mem xD,Finset.card_univ]
    omega
  obtain ⟨z,_,zOut⟩ := Finset.exists_mem_not_mem_of_card_lt_card someOutside
  have zD : z ∉ D := fun h => zOut (Finset.mem_insert_of_mem h)
  let u : Survives D := ⟨x,xD⟩
  let v : Survives D := ⟨z,zD⟩
  have noreach : ∀ w : Survives D, ¬ (G.induce {v | v ∉ D}).Adj u w :=
    fun w h => w.property ((G.mem_neighborFinset _ _).mpr h)
  have uv := isolated_reachable_eq noreach (below D count u v)
  have xz : x = z := congrArg Subtype.val uv
  exact zOut (xz ▸ Finset.mem_insert_self _ _)

/-- Whole graph lift with the two explicit cut assumptions and with the
canonical exclusion of degree three at the first loose port. -/
theorem depleted_footprint_with_canonical_cut_data {loss : Bool} (F : DepletedFootprint G loss)
    (below : ∀ D : Finset V, D.card < 3 → (G.induce {v | v ∉ D}).Preconnected)
    (three : ∀ D : Finset V, D.card = 3 →
      (G.induce {v | v ∉ D}).Preconnected ∨
        ∃ s : Survives D, (∀ t : Survives D, ¬ G.Adj s.val t.val) ∧
          ∀ x y : Survives D, x ≠ s → y ≠ s → (G.induce {v | v ∉ D}).Reachable x y)
    (looseOff : G.degree (F.inner 3) ≠ 3) :
    (Fintype.card V = if loss then 15 else 16) ∧ Nonempty (PathOn G Set.univ) := by
  obtain ⟨L,_,_⟩ := F.normalize
  have order := L.order
  have size : 4 ≤ Fintype.card V := by cases loss <;> simp_all
  exact depleted_footprint_of_singleton_cuts F below three
    (degree_of_small_deletion_preconnected size below (F.inner 3)) looseOff

#print axioms degree_of_small_deletion_preconnected
#print axioms depleted_footprint_with_canonical_cut_data

end Graffiti199Depleted
