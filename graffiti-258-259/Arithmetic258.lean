import Std

namespace Graffiti258

/-- One Boolean per vertex along a path; true means even BFS level. -/
def evenCount : List Bool → Nat
  | [] => 0
  | true :: xs => 1 + evenCount xs
  | false :: xs => evenCount xs

def Alternates : List Bool → Prop
  | [] => True
  | [_] => True
  | x :: y :: xs => x ≠ y ∧ Alternates (y :: xs)

theorem alternating_path_bound (xs : List Bool) (h : Alternates xs) :
    2 * evenCount xs ≤ xs.length + 1 := by
  match xs with
  | [] => decide
  | [x] => cases x <;> decide
  | x :: y :: xs =>
    have hxy := h.1
    have hs : Alternates xs := by
      cases xs with
      | nil => trivial
      | cons z zs => exact h.2.2
    have ht := alternating_path_bound xs hs
    cases x <;> cases y <;> simp_all [evenCount]
    all_goals omega

def forestEven : List (List Bool) → Nat
  | [] => 0
  | xs :: xss => evenCount xs + forestEven xss

def forestSize : List (List Bool) → Nat
  | [] => 0
  | xs :: xss => xs.length + forestSize xss

/-- Adds the individual bounds along any path decomposition. -/
theorem alternating_forest_bound (P : List (List Bool)) (h : ∀ p ∈ P, Alternates p) :
    2 * forestEven P ≤ forestSize P + P.length := by
  induction P with
  | nil => decide
  | cons p ps ih =>
    have hp := alternating_path_bound p (h p (by simp))
    have hps := ih (fun q hq => h q (by simp [hq]))
    simp only [forestEven, forestSize, List.length_cons]
    omega

/-- Numeric endgame: t is total domination, L max leaves, E even shell size. 
The disjunct supplies either the leaf/root star case, the degree-two case,
or the general-case premises proved combinatorially. -/
theorem arithmetic_shared (n t L E : Nat) (ht : 2 ≤ t)
    (h : (t = 2 ∧ E ≤ L) ∨
         (L = 2 ∧ E ≤ t) ∨
         (3 ≤ L ∧ E + 2 ≤ n ∧ n + 2 ≤ L + 2*t ∧
         (L = 3 → 4 ≤ t → 2*E ≤ 3*t) ∧ (t ≤ 3 → n ≤ L + t))) :
    2*E ≤ t*L := by
  rcases h with h | h | h
  · rcases h with ⟨rfl, h⟩
    omega
  · rcases h with ⟨rfl, h⟩
    omega
  · rcases h with ⟨hL, hEn, hnt, he3, hts⟩
    by_cases h3 : L = 3
    · subst L
      by_cases hs : t ≤ 3
      · have hc := hts hs
        omega
      · simpa only [Nat.mul_comm 3 t] using (he3 rfl (by omega))
    · let a := t - 2
      let b := L - 4
      have hta : t = a + 2 := by dsimp [a]; omega
      have hLb : L = b + 4 := by dsimp [b]; omega
      calc
        2*E ≤ 2*b + 4*a + 8 := by omega
        _ ≤ a*b + (2*b + 4*a + 8) := by omega
        _ = t*L := by
          rw [hta, hLb]
          simp only [Nat.add_mul, Nat.mul_add]
          omega

theorem arithmetic_258 (n t L E : Nat) (ht : 2 ≤ t)
    (h : (t = 2 ∧ E ≤ L) ∨
         (L = 2 ∧ E ≤ t) ∨
         (3 ≤ L ∧ E + 2 ≤ n ∧ n + 2 ≤ L + 2*t ∧
         (L = 3 → 2*E ≤ n + 3) ∧ (t ≤ 3 → n ≤ L + t))) :
    2*E ≤ t*L := by
  apply arithmetic_shared n t L E ht
  rcases h with h | h | ⟨hL, hEn, hnt, h3, hts⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨hL, hEn, hnt, fun hh ht4 => by have := h3 hh; omega, hts⟩)

theorem arithmetic_259 (n t L X : Nat) (ht : 2 ≤ t)
    (h : (t = 2 ∧ X ≤ L) ∨
         (L = 2 ∧ X ≤ t) ∨
         (3 ≤ L ∧ X + 2 ≤ n ∧ n + 2 ≤ L + 2*t ∧
         (L = 3 → X ≤ 6) ∧ (t ≤ 3 → n ≤ L + t))) :
    2*X ≤ t*L := by
  apply arithmetic_shared n t L X ht
  rcases h with h | h | ⟨hL, hXn, hnt, h3, hts⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨hL, hXn, hnt, fun hh ht4 => by have := h3 hh; omega, hts⟩)

#print axioms alternating_forest_bound
#print axioms arithmetic_258
#print axioms arithmetic_259

end Graffiti258
