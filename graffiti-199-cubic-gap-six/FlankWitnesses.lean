import FlankRules

namespace Graffiti199Depleted.WiderOmission

open CompactOmission (SixTree)

inductive FlankWitness (n k : ℕ)
  | tree (order : Fin 6 → Fin ((n+1)+k))
  | route (order : List (Fin (n+1))) (front : Bool)
  | pass

def FlankWitness.Valid {n k : ℕ} (e : Fin ((n+1)+k) → Fin ((n+1)+k) → Bool)
    (route : List (Fin (n+1)) → Bool → Prop) (pass : Prop) : FlankWitness n k → Prop
  | .tree T => SixTree e T
  | .route P front => route P front
  | .pass => pass

instance decidableFlankWitnessValid {n k : ℕ} (e : Fin ((n+1)+k) → Fin ((n+1)+k) → Bool)
    (route : List (Fin (n+1)) → Bool → Prop) [∀ P f, Decidable (route P f)]
    (pass : Prop) [Decidable pass] (w : FlankWitness n k) :
    Decidable (w.Valid e route pass) := by cases w <;> unfold FlankWitness.Valid <;> infer_instance

def PairValidation {n : ℕ} (e : Fin (n+1) → Fin (n+1) → Bool) (profiles : List ℕ)
    (boundary : ℕ) (cert : ℕ → ℕ → Bool → FlankWitness n 2) : Prop :=
  ∀ (i j : Fin profiles.length) (b : Bool),
    let m := profiles.get i
    let q := profiles.get j
    touch m (0 : Fin (n+1)) = true → touch q (rightEnd n) = true →
      (cert m q b).Valid (pairEdge e m q b) (fun P _ => PairRoute (pairEdge e m q b) P)
        (m = boundary ∧ q = boundary ∧ b = true)

def StepValidation {n : ℕ} (e : Fin (n+1) → Fin (n+1) → Bool) (profiles : List ℕ)
    (boundary : ℕ) (cert : ℕ → Bool → FlankWitness n 3) : Prop :=
  ∀ (i : Fin profiles.length) (b : Bool),
    let m := profiles.get i
    (cert m b).Valid (stepEdge e boundary m b) (StepRoute (stepEdge e boundary m b))
      (m = boundary ∧ b = true)

instance {n : ℕ} (e : Fin (n+1) → Fin (n+1) → Bool) (profiles : List ℕ)
    (boundary : ℕ) (cert : ℕ → ℕ → Bool → FlankWitness n 2) :
    Decidable (PairValidation e profiles boundary cert) := by unfold PairValidation; infer_instance

instance {n : ℕ} (e : Fin (n+1) → Fin (n+1) → Bool) (profiles : List ℕ)
    (boundary : ℕ) (cert : ℕ → Bool → FlankWitness n 3) :
    Decidable (StepValidation e profiles boundary cert) := by unfold StepValidation; infer_instance

theorem certify_pair {n : ℕ} {e : Fin (n+1) → Fin (n+1) → Bool} {profiles : List ℕ}
    {boundary : ℕ} {cert : ℕ → ℕ → Bool → FlankWitness n 2}
    (valid : PairValidation e profiles boundary cert)
    (m q : ℕ) (b : Bool) (hm : m ∈ profiles) (hq : q ∈ profiles)
    (left : touch m (0 : Fin (n+1)) = true) (right : touch q (rightEnd n) = true) :
    (∃ T, SixTree (pairEdge e m q b) T) ∨ (∃ P, PairRoute (pairEdge e m q b) P) ∨
      (m = boundary ∧ q = boundary ∧ b = true) := by
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hm
  obtain ⟨j,rfl⟩ := List.mem_iff_get.mp hq
  have test := valid i j b left right
  cases h : cert (profiles.get i) (profiles.get j) b with
  | tree T => rw [h] at test; exact Or.inl ⟨T,test⟩
  | route P _ => rw [h] at test; exact Or.inr (Or.inl ⟨P,test⟩)
  | pass => rw [h] at test; exact Or.inr (Or.inr test)

theorem certify_step {n : ℕ} {e : Fin (n+1) → Fin (n+1) → Bool} {profiles : List ℕ}
    {boundary : ℕ} {cert : ℕ → Bool → FlankWitness n 3}
    (valid : StepValidation e profiles boundary cert)
    (m : ℕ) (b : Bool) (hm : m ∈ profiles) :
    (∃ T, SixTree (stepEdge e boundary m b) T) ∨
      (∃ P front, StepRoute (stepEdge e boundary m b) P front) ∨
      (m = boundary ∧ b = true) := by
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hm
  have test := valid i b
  dsimp only at test
  cases h : cert (profiles.get i) b with
  | tree T => rw [h] at test; exact Or.inl ⟨T,test⟩
  | route P front => rw [h] at test; exact Or.inr (Or.inl ⟨P,front,test⟩)
  | pass => rw [h] at test; exact Or.inr (Or.inr test)

end Graffiti199Depleted.WiderOmission
