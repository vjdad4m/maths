import CompactGraphLifts
import CompactSingleRows

open private code_profile no_external_at_cubic from CompactGraphLifts

namespace Graffiti199Depleted.CompactOmission

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}
variable [DecidableEq V] [DecidableRel G.Adj] [Fintype V]

theorem external_profile (budget : Catalogue.treeNumber G ≤ 5)
    {f : Fin 8 ↪ V} {k : Fin 6} {v : V}
    (core : ∀ i j, G.Adj (f i) (f j) ↔ adjacent (coreRows k) i j = true)
    (dz : G.degree (f 7) = 3) (dm : G.degree (f (mate k)) = 3)
    (off : ∀ i, v ≠ f i) : ∃ m ∈ profiles k, ProfileAt G f v m := by
  have noZ := no_external_at_cubic f off (a := 1) (b := 3) (c := 5) (by decide)
    (by decide) (by decide) dz ((core _ _).mpr rfl) ((core _ _).mpr rfl) ((core _ _).mpr rfl)
  have noMate : ¬ G.Adj v (f (mate k)) := by
    have bcase (eq : mate k = 3) : ¬ G.Adj v (f (mate k)) := by
      rw [eq] at dm ⊢
      exact no_external_at_cubic f off (a := 2) (b := 4) (c := 7) (by decide)
        (by decide) (by decide) dm ((core _ _).mpr rfl) ((core _ _).mpr rfl) ((core _ _).mpr rfl)
    have acase (eq : mate k = 1) : ¬ G.Adj v (f (mate k)) := by
      rw [eq] at dm ⊢
      exact no_external_at_cubic f off (a := 0) (b := 2) (c := 7) (by decide)
        (by decide) (by decide) dm ((core _ _).mpr rfl) ((core _ _).mpr rfl) ((core _ _).mpr rfl)
    have ccase (eq : mate k = 5) : ¬ G.Adj v (f (mate k)) := by
      rw [eq] at dm ⊢
      exact no_external_at_cubic f off (a := 4) (b := 6) (c := 7) (by decide)
        (by decide) (by decide) dm ((core _ _).mpr rfl) ((core _ _).mpr rfl) ((core _ _).mpr rfl)
    fin_cases k <;> first | exact bcase rfl | exact acase rfl | exact ccase rfl
  obtain ⟨m,hm⟩ := code_profile f v noZ
  have offBit : contact m (mate k) = false := Bool.eq_false_iff.mpr (fun h => noMate ((hm _).mpr h))
  rcases single_extension k m offBit with good|⟨T,tree⟩
  · exact ⟨m,good,hm⟩
  · let x : Fin 1 ↪ V := ⟨fun _ => v,fun _ _ _ => Subsingleton.elim _ _⟩
    let g := extend f x (fun i _ => off i)
    have chart : ∀ i j, G.Adj (g i) (g j) ↔ oneEdge k m i j = true :=
      extension_chart core (fun _ => hm) (fun _ _ => by simp [x])
    exact (six_tree_absurd budget chart tree).elim

#print axioms external_profile

end Graffiti199Depleted.CompactOmission
