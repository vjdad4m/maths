import DominatingPentagon133

namespace Graffiti133FarPentagon
open SimpleGraph Graffiti133 Graffiti133Revisit Graffiti133NoFive Finset
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
universe u

variable {V : Type u} [Fintype V]

def Finding (G : SimpleGraph V) : Prop :=
  (∃ f : Fin 7 → V, InducedPath G f) ∨ Nonempty (Hole G 6) ∨ Nonempty (Hole G 7)

private theorem connected_peel_finding (G : SimpleGraph V) (hc : G.Connected)
    (h4 : FourCycleFree G)
    (hD : 3*Fintype.card V ≤ (∑ v, localIndependence G v))
    (core : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W), J.Connected →
      FourCycleFree J → (∀ v, 2 ≤ localIndependence J v) →
      3*Fintype.card W ≤ (∑ v, localIndependence J v) →
      Finding J) :
    Finding G := by
  classical
  let Claim (n : ℕ) := ∀ (W : Type u) [Fintype W] (J : SimpleGraph W),
    Fintype.card W=n → J.Connected → FourCycleFree J →
    3*Fintype.card W ≤ (∑ v, localIndependence J v) →
    Finding J
  have aux (n : ℕ) : Claim n := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W _ G hn hC h4 dens
      letI := hC.nonempty
      by_cases hmin : ∀ v, 2 ≤ localIndependence G v
      · exact core W G hC h4 hmin dens
      push_neg at hmin
      obtain ⟨v,hv⟩ := hmin
      let S : Set W := {w | w ≠ v}
      let H := G.induce S
      have hpos : 0 < Fintype.card W := Fintype.card_pos
      have hS : Fintype.card S + 1 = Fintype.card W := by
        have hs : Fintype.card S = Fintype.card W - 1 := by
          change Fintype.card {x : W // ¬ x = v} = _
          rw [Fintype.card_subtype_compl]
          rw [show Fintype.card {x : W // x = v} = 1 from Fintype.card_unique]
        omega
      have h4' : FourCycleFree H := by
        intro a b x y hab hax hbx hay hby
        apply Subtype.ext
        exact h4 _ _ _ _ (fun h => hab (Subtype.ext h)) hax hbx hay hby
      have non : Nonempty S := by
        have pos : 0 < (∑ v, localIndependence G v) := by omega
        obtain ⟨a,b,ab⟩ : ∃ a b, G.Adj a b := by
          apply Classical.byContradiction
          intro no
          have eq : ∀ x, localIndependence G x = 0 := by
            intro x
            obtain ⟨A,hA,hc⟩ := Graffiti133Pentagon.PentagonFrame.maxLocalSet (G:=G) x
            rw [← hc,Finset.card_eq_zero]
            apply Finset.not_nonempty_iff_eq_empty.mp
            rintro ⟨a,ha⟩
            exact no ⟨x,a,(Graffiti133Pentagon.PentagonFrame.memLocalSet.mp hA).1 a ha⟩
          simp [eq] at pos
        by_cases ha : a=v
        · exact ⟨⟨b,(ha ▸ ab.ne).symm⟩⟩
        · exact ⟨⟨a,ha⟩⟩
      have hConn : H.Connected := connected_delete_low_local G hC v (by omega) non
      have loss := local_sum_delete_bound G h4 v
      have dH : 3*Fintype.card S ≤ (∑ w, localIndependence H w) := by
        rw [← hS,Nat.mul_add,Nat.mul_one] at dens
        change (∑ w, localIndependence G w) ≤ (∑ w : S, localIndependence H w) +
          2*localIndependence G v at loss
        omega
      have witness := ih _ (by omega : Fintype.card S < n) S H rfl hConn h4' dH
      rcases witness with p | a | b
      · obtain ⟨f,hf⟩ := p
        exact Or.inl ⟨fun i => (f i).val,Subtype.val_injective.comp hf.1,hf.2⟩
      · obtain ⟨H⟩ := a
        exact Or.inr (Or.inl ⟨⟨fun i => (H.c i).val,Subtype.val_injective.comp H.inj,H.adj⟩⟩)
      · obtain ⟨H⟩ := b
        exact Or.inr (Or.inr ⟨⟨fun i => (H.c i).val,Subtype.val_injective.comp H.inj,H.adj⟩⟩)
  exact aux (Fintype.card V) V G rfl hc h4 hD

/-- If a connected C4-free graph has mean local independence at least three,
it contains an induced P7, an induced C6, or an induced C7. -/
theorem local_mean_three_path_or_hole (G : SimpleGraph V) (hc : G.Connected)
    (h4 : FourCycleFree G) (hA : 3 ≤ averageLocal G) :
    Finding G := by
  classical
  letI := hc.nonempty
  apply connected_peel_finding G hc h4 (nat_density_of_le_average G 3 hA)
  intro W _ J conn h4 min hsum
  letI := conn.nonempty
  by_cases h5 : NoSimpleFive133 J
  · have av : 3 ≤ averageLocal J := by
      unfold averageLocal
      have hpos : (0 : ℚ) < Fintype.card W := by exact_mod_cast Fintype.card_pos (α:=W)
      apply (le_div_iff₀ hpos).mpr
      rw [← Nat.cast_sum]
      exact_mod_cast hsum
    exact Or.inl (P7_of_mean_three_no_five J conn h4 h5 av)
  · by_cases yes7 : ∃ f : Fin 7 → W, InducedPath J f
    · exact Or.inl yes7
    · by_cases yesH : Nonempty (Hole J 6) ∨ Nonempty (Hole J 7)
      · exact Or.inr yesH
      · exfalso
        obtain ⟨F⟩ := build_frame h4 h5
        have dom (x : W) (hx : ∀ i, x ≠ F.c i) : Near F x := by
          refine ⟨hx,?_⟩
          apply Classical.byContradiction
          intro unknown
          have far : Far F x := ⟨hx,fun i e => unknown ⟨i,e⟩⟩
          exact yesH (F.far_forces_hole conn yes7 min far)
        have hB := F.pent_budget dom (fun he => yesH (Or.inl he))
        omega

#print axioms local_mean_three_path_or_hole

end Graffiti133FarPentagon
