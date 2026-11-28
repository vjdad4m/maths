import Threshold
import Cases.K0
import Cases.K1
import Cases.K2
import Cases.K3
import Cases.K4
import Cases.K5
import Cases.K6
import Cases.K7
import Cases.K8
import Cases.K9
import Cases.K10
import Cases.K11
import Cases.K12
import Cases.K13
import Cases.K14
import Cases.K15
import Cases.K16
import Cases.K17
import Cases.K18
import Cases.K19
import Cases.K20
import Cases.K21
import Cases.K22
import Cases.K23

namespace BadScienceSeven
theorem verified (k : Fin 24) (a : Nat) (ha : a < k.val / 2 + 1) : checkPrefix k.val a = true := by
  have h : k.val = 0 ∨ k.val = 1 ∨ k.val = 2 ∨ k.val = 3 ∨ k.val = 4 ∨ k.val = 5 ∨ k.val = 6 ∨ k.val = 7 ∨ k.val = 8 ∨ k.val = 9 ∨ k.val = 10 ∨ k.val = 11 ∨ k.val = 12 ∨ k.val = 13 ∨ k.val = 14 ∨ k.val = 15 ∨ k.val = 16 ∨ k.val = 17 ∨ k.val = 18 ∨ k.val = 19 ∨ k.val = 20 ∨ k.val = 21 ∨ k.val = 22 ∨ k.val = 23 := by omega
  rcases h with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
  · rw [h]
    exact show checkPrefix 0 a = true from verified0 ⟨a, by have hh := ha; rw [h] at hh; exact hh⟩
  · rw [h]
    exact show checkPrefix 1 a = true from verified1 ⟨a, by have hh := ha; rw [h] at hh; exact hh⟩
  · rw [h]
    exact show checkPrefix 2 a = true from verified2 ⟨a, by have hh := ha; rw [h] at hh; exact hh⟩
  · rw [h]
    exact show checkPrefix 3 a = true from verified3 ⟨a, by have hh := ha; rw [h] at hh; exact hh⟩
  · rw [h]
    exact show checkPrefix 4 a = true from verified4 ⟨a, by have hh := ha; rw [h] at hh; exact hh⟩
  · rw [h]
    exact show checkPrefix 5 a = true from verified5 ⟨a, by have hh := ha; rw [h] at hh; exact hh⟩
  · rw [h]
    exact show checkPrefix 6 a = true from verified6 ⟨a, by have hh := ha; rw [h] at hh; exact hh⟩
  · rw [h]
    exact show checkPrefix 7 a = true from verified7 ⟨a, by have hh := ha; rw [h] at hh; exact hh⟩
  · rw [h]
    exact show checkPrefix 8 a = true from verified8 ⟨a, by have hh := ha; rw [h] at hh; exact hh⟩
  · rw [h]
    exact show checkPrefix 9 a = true from verified9 ⟨a, by have hh := ha; rw [h] at hh; exact hh⟩
  · rw [h]
    exact show checkPrefix 10 a = true from verified10 ⟨a, by have hh := ha; rw [h] at hh; exact hh⟩
  · rw [h]
    exact show checkPrefix 11 a = true from verified11 ⟨a, by have hh := ha; rw [h] at hh; exact hh⟩
  · rw [h]
    exact show checkPrefix 12 a = true from verified12 ⟨a, by have hh := ha; rw [h] at hh; exact hh⟩
  · rw [h]
    exact show checkPrefix 13 a = true from verified13 ⟨a, by have hh := ha; rw [h] at hh; exact hh⟩
  · rw [h]
    exact show checkPrefix 14 a = true from verified14 ⟨a, by have hh := ha; rw [h] at hh; exact hh⟩
  · rw [h]
    exact show checkPrefix 15 a = true from verified15 ⟨a, by have hh := ha; rw [h] at hh; exact hh⟩
  · rw [h]
    exact show checkPrefix 16 a = true from verified16 ⟨a, by have hh := ha; rw [h] at hh; exact hh⟩
  · rw [h]
    exact show checkPrefix 17 a = true from verified17 ⟨a, by have hh := ha; rw [h] at hh; exact hh⟩
  · rw [h]
    exact show checkPrefix 18 a = true from verified18 ⟨a, by have hh := ha; rw [h] at hh; exact hh⟩
  · rw [h]
    exact show checkPrefix 19 a = true from verified19 ⟨a, by have hh := ha; rw [h] at hh; exact hh⟩
  · rw [h]
    exact show checkPrefix 20 a = true from verified20 ⟨a, by have hh := ha; rw [h] at hh; exact hh⟩
  · rw [h]
    exact show checkPrefix 21 a = true from verified21 ⟨a, by have hh := ha; rw [h] at hh; exact hh⟩
  · rw [h]
    exact show checkPrefix 22 a = true from verified22 ⟨a, by have hh := ha; rw [h] at hh; exact hh⟩
  · rw [h]
    exact show checkPrefix 23 a = true from verified23 ⟨a, by have hh := ha; rw [h] at hh; exact hh⟩

#print axioms verified
end BadScienceSeven
