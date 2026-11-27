import HandleCuts
import FourRingCyclicEquivalence

namespace KelmansCactus.AtomicBridge.HandleExtension.Edges
open SimpleGraph Finset FourRingCutAux FourRingCyclicEquivalence
set_option linter.unusedSectionVars false
noncomputable section
variable {V : Type*} {G : SimpleGraph V} (E : Edges G)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem old_eq_delete_two :
    (Old : Set (V ⊕ Bool)) = {x | x ≠ Sum.inr false ∧ x ≠ Sum.inr true} := by
  ext x
  cases x with
  | inl x => simp [Old]
  | inr s => cases s <;> simp [Old]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Deleting the two new endpoints leaves exactly the old graph with the
two selected edges deleted, up to the canonical vertex relabeling. -/
def deleted_two_iso : E.deleteChosen ≃g
    E.host.induce {x | x ≠ Sum.inr false ∧ x ≠ Sum.inr true} := by
  rw [← old_eq_delete_two]
  exact E.deleted_iso

theorem host_order : Fintype.card (V ⊕ Bool) = Fintype.card V + 2 := by
  rw [Fintype.card_sum, Fintype.card_bool]

include E in
theorem host_order_ge_four : 4 ≤ Fintype.card (V ⊕ Bool) := by
  classical
  have h := Finset.card_le_univ (s := ({E.a false,E.b false} : Finset V))
  have hn := (E.edge false).ne
  have hcard : 2 ≤ Fintype.card V := by simpa [hn] using h
  rw [host_order]
  omega

/-- The edge-cut preservation theorem also supplies 3-vertex-connectivity. -/
theorem three_connected (cub : ∀ x,G.degree x=3) (small : SmallTrivial G) :
    KelmansStarter.ThreeConnected E.host :=
  three_connected_of_small_trivial E.host (E.cubic cub) (E.host_order_ge_four)
    (E.preserves_small_trivial cub small)

theorem preserves_no_cyclic_cut (cub : ∀ x,G.degree x=3) (oldCyc : NoCyclicCutBelowFour G) :
    NoCyclicCutBelowFour E.host := by
  exact (small_trivial_iff_no_cyclic_cut E.host (E.cubic cub)).mp
    (E.preserves_small_trivial cub ((small_trivial_iff_no_cyclic_cut G cub).mpr oldCyc))

/-- This is the exact hypothesis package needed by `CyclicUniversal`
when the handle raises the old order to a multiple of six. -/
theorem cyclic_domain (cub : ∀ x,G.degree x=3) (small : SmallTrivial G)
    (div : 6 ∣ Fintype.card V+2) : CyclicDomain E.host := by
  refine ⟨⟨E.cubic cub,E.three_connected cub small,?_⟩,E.preserves_small_trivial cub small⟩
  rwa [host_order]

#print axioms deleted_two_iso
#print axioms three_connected
#print axioms preserves_no_cyclic_cut
#print axioms cyclic_domain
end
end KelmansCactus.AtomicBridge.HandleExtension.Edges
