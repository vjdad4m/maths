import PowerBasis

namespace Book567
open SimpleGraph Finset AutoGraphPowerBurning

/-- A power-dominating seed must hit the closed neighborhood of every
pair of distinct vertices with the same open neighborhood. -/
theorem hit_twins {U : Type*} (G : SimpleGraph U) {a b : U} (ne : a ≠ b)
    (twins : ∀ w, G.Adj a w ↔ G.Adj b w) (S : Finset U) (observed : Observed G S a) :
    ∃ w ∈ S, w = a ∨ w = b ∨ G.Adj a w := by
  classical
  by_contra! missed
  have exclude {v} (h : Observed G S v) : v ≠ a ∧ v ≠ b := by
    induction h with
    | root hv => exact ⟨(missed _ hv).1,(missed _ hv).2.1⟩
    | neighbor hw e =>
      exact ⟨fun eq => (missed _ hw).2.2 (eq ▸ e),
        fun eq => (missed _ hw).2.2 ((twins _).mpr (eq ▸ e))⟩
    | @force v w e _ _ _ ih =>
      constructor
      · rintro rfl
        exact (ih b ((twins w).mp e).symm ne.symm).2 rfl
      · rintro rfl
        exact (ih a ((twins w).mpr e).symm ne).1 rfl
  exact (exclude observed).1 rfl

end Book567
