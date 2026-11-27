import PentagonStructure133

namespace Graffiti133Revisit
open SimpleGraph Graffiti133 Graffiti133RevisitSix Finset
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

private theorem lift_strict_two (k : ℕ)
    (G : SimpleGraph V) [Nonempty V] (h4 : FourCycleFree G)
    (hD : 2*Fintype.card V + 1 ≤ (∑ x, localIndependence G x))
    (witness : ∀ (W : Type u) [Fintype W] [Nonempty W] (J : SimpleGraph W) (e : W ↪ V),
      (∀ a b, J.Adj a b ↔ G.Adj (e a) (e b)) → FourCycleFree J →
      (∀ x, 2 ≤ localIndependence J x) →
      2*Fintype.card W + 1 ≤ (∑ x, localIndependence J x) →
      ∃ f : Fin k → W, InducedPath J f) :
    ∃ f : Fin k → V, InducedPath G f := by
  classical
  let Claim (n : ℕ) := ∀ (W : Type u) [Fintype W] [DecidableEq W] [Nonempty W],
    Fintype.card W = n → ∀ (J : SimpleGraph W) (e : W ↪ V),
    (∀ a b, J.Adj a b ↔ G.Adj (e a) (e b)) → FourCycleFree J →
    2*Fintype.card W + 1 ≤ (∑ x, localIndependence J x) →
    ∃ f : Fin k → W, InducedPath J f
  have aux (n : ℕ) : Claim n := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W _ _ _ hn G e hEmbed h4 dens
      by_cases hh : ∀ v, 2 ≤ localIndependence G v
      · exact witness W G e hEmbed h4 hh dens
      push_neg at hh
      obtain ⟨v,hv⟩ := hh
      let S : Set W := {x | x ≠ v}
      let H := G.induce S
      have hpos : 0 < Fintype.card W := Fintype.card_pos
      have hS : Fintype.card S + 1 = Fintype.card W := by
        have hs : Fintype.card S = Fintype.card W - 1 := by
          change Fintype.card {x : W // ¬ x = v} = _
          rw [Fintype.card_subtype_compl]
          rw [show Fintype.card {x : W // x = v} = 1 from Fintype.card_unique]
        omega
      have hFree : FourCycleFree H := by
        intro a b x y hab hax hbx hay hby
        apply Subtype.ext
        exact h4 _ _ _ _ (fun h => hab (Subtype.ext h)) hax hbx hay hby
      have posSum : 0 < (∑ x, localIndependence G x) := by omega
      have edg : ∃ a b, G.Adj a b := by
        apply Classical.byContradiction
        intro no
        have nn : ∀ x, localIndependence G x = 0 := by
          intro x
          obtain ⟨A,hA,hAC⟩ := Graffiti133Pentagon.PentagonFrame.maxLocalSet (G:=G) x
          rw [← hAC,Finset.card_eq_zero]
          apply Finset.not_nonempty_iff_eq_empty.mp
          intro hne
          obtain ⟨a,ha⟩ := hne
          exact no ⟨x,a,(Graffiti133Pentagon.PentagonFrame.memLocalSet.mp hA).1 a ha⟩
        simp [nn] at posSum
      obtain ⟨a,b,hab⟩ := edg
      haveI : Nonempty S := by
        by_cases eq : a = v
        · exact ⟨⟨b,(eq ▸ hab.ne).symm⟩⟩
        · exact ⟨⟨a,eq⟩⟩
      have hloss := local_sum_delete_bound G h4 v
      have hD' : 2*Fintype.card S + 1 ≤ (∑ x, localIndependence H x) := by
        rw [← hS,Nat.mul_add,Nat.mul_one] at dens
        change (∑ x, localIndependence G x) ≤ (∑ x : S, localIndependence H x) +
          2*localIndependence G v at hloss
        omega
      have hsN : Fintype.card S < n := by omega
      obtain ⟨f,hf⟩ := ih _ hsN S rfl H ((Function.Embedding.subtype _).trans e)
        (fun a b => hEmbed a.val b.val) hFree hD'
      exact ⟨fun i => (f i).val,Subtype.val_injective.comp hf.1,hf.2⟩
  exact aux (Fintype.card V) V rfl G (Function.Embedding.refl V) (fun _ _ => Iff.rfl) h4 hD

/-- In a nonempty four- and five-cycle-free graph, local mean strictly
above two forces an induced P6. -/
theorem P6_of_local_mean_gt_two_without_five (G : SimpleGraph V) [Nonempty V]
    (h4 : FourCycleFree G) (h5 : NoSimpleFive133 G) (hA : 2 < averageLocal G) :
    ∃ f : Fin 6 → V, InducedPath G f := by
  classical
  have hD : 2 * Fintype.card V < (∑ x, localIndependence G x) := by
    unfold averageLocal at hA
    have hn : (0 : ℚ) < Fintype.card V := by exact_mod_cast Fintype.card_pos (α := V)
    have hh := (lt_div_iff₀ hn).mp hA
    rw [← Nat.cast_sum] at hh
    have hh' : ((2 * Fintype.card V : ℕ) : ℚ) < ((∑ x, localIndependence G x : ℕ) : ℚ) := by
      simpa using hh
    exact_mod_cast hh'
  apply lift_strict_two 6 G h4 (by omega)
  intro W _ _ J emb hj h4J hmin hD'
  have h5J : NoSimpleFive133 J := by
    intro a b c d e hn e1 e2 e3 e4 e5
    have hx := hn.map emb.injective
    exact h5 _ _ _ _ _ (by simpa using hx) ((hj _ _).mp e1)
      ((hj _ _).mp e2) ((hj _ _).mp e3) ((hj _ _).mp e4) ((hj _ _).mp e5)
  obtain ⟨v,hv⟩ : ∃ v, 3 ≤ localIndependence J v := by
    apply Classical.byContradiction
    intro no
    have hBound (x : W) : localIndependence J x ≤ 2 := by
      have : localIndependence J x < 3 := Nat.lt_of_not_ge (fun h => no ⟨x,h⟩)
      omega
    have ht : (∑ x, localIndependence J x) ≤ 2 * Fintype.card W := by
      have hh := Finset.sum_le_sum (s := (Finset.univ : Finset W)) (fun x _ => hBound x)
      simpa [Nat.mul_comm] using hh
    omega
  exact six_path_of_min_and_high h4J h5J hmin v hv

#print axioms P6_of_local_mean_gt_two_without_five
end Graffiti133Revisit
