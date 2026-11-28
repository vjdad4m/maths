import Mathlib.Data.Nat.Basic

/-! Arithmetic for the six-centre count.  This file needs no graph hypotheses. -/
namespace Graffiti189SixCentre

def evenBit (n : ℕ) : ℕ := if n % 2 = 0 then 1 else 0

/-- Coverage by the two terminals and a port of each, the ports
being on the opposite side of a two-vertex separator. -/
def coverage (a b u v : ℕ) : ℕ :=
  evenBit a + evenBit b + evenBit (min (a + 1) (b + u)) +
    evenBit (min (a + v) (b + 1))

theorem coverage_swap (a b u v : ℕ) :
    coverage a b u v = coverage b a v u := by
  unfold coverage
  rw [min_comm (b + 1) (a + v), min_comm (b + u) (a + 1)]
  omega

/-- The entries where the distance to the first terminal is greater.
The other entries are obtained by interchanging the two terminals. -/
def entry (gap base opposite : ℕ) : ℕ :=
  if gap ≤ 1 then 2
  else if gap = 2 then
    if base % 2 = 0 then 2 + (if opposite = 2 then 1 else 0)
    else 1 + (if 3 ≤ opposite then 1 else 0)
  else
    if base % 2 = 0 then 1 + evenBit opposite
    else 3 - evenBit opposite

theorem evenBit_add_mod (b k : ℕ) : evenBit (b + k) = evenBit (b % 2 + k) := by
  unfold evenBit
  have h : (b + k) % 2 = (b % 2 + k) % 2 := by omega
  rw [h]

theorem coverage_translate (b k u v : ℕ) :
    coverage (b + k) b u v =
      coverage (b % 2 + k) (b % 2) u v := by
  unfold coverage
  rw [show min (b + k + 1) (b + u) = b + min (k + 1) u by
    rw [Nat.add_assoc, Nat.add_min_add_left]]
  rw [show min (b + k + v) (b + 1) = b + min (k + v) 1 by
    rw [Nat.add_assoc, Nat.add_min_add_left]]
  rw [show min (b % 2 + k + 1) (b % 2 + u) = b % 2 + min (k + 1) u by
    rw [Nat.add_assoc, Nat.add_min_add_left]]
  rw [show min (b % 2 + k + v) (b % 2 + 1) = b % 2 + min (k + v) 1 by
    rw [Nat.add_assoc, Nat.add_min_add_left]]
  rw [evenBit_add_mod, evenBit_add_mod b (min (k + 1) u),
    evenBit_add_mod b (min (k + v) 1)]
  rw [show evenBit b = evenBit (b % 2) by simp [evenBit]]

theorem coverage_table_right (b k u v : ℕ)
    (hk : k ≤ 3) (hu₁ : 2 ≤ u) (hu₂ : u ≤ 4)
    (hv₁ : 2 ≤ v) (hv₂ : v ≤ 4) :
    coverage (b + k) b u v = entry k b u := by
  rw [coverage_translate]
  have hb : b % 2 < 2 := Nat.mod_lt _ (by decide)
  have e : entry k b u = entry k (b % 2) u := by
    simp only [entry, Nat.mod_mod]
  rw [e]
  generalize b % 2 = c at hb ⊢
  have hc : c = 0 ∨ c = 1 := by omega
  have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  have hu' : u = 2 ∨ u = 3 ∨ u = 4 := by omega
  have hv' : v = 2 ∨ v = 3 ∨ v = 4 := by omega
  rcases hc with rfl|rfl <;> rcases hk' with rfl|rfl|rfl|rfl <;> rcases hu' with rfl|rfl|rfl <;> rcases hv' with rfl|rfl|rfl <;> decide

theorem coverage_table (a b u v : ℕ)
    (hab : a ≤ b + 3) (hba : b ≤ a + 3)
    (hu₁ : 2 ≤ u) (hu₂ : u ≤ 4) (hv₁ : 2 ≤ v) (hv₂ : v ≤ 4) :
    coverage a b u v =
      if b ≤ a then entry (a - b) b u else entry (b - a) a v := by
  split
  · rename_i h
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [Nat.add_sub_cancel_left]
    exact coverage_table_right b k u v (by omega) hu₁ hu₂ hv₁ hv₂
  · rename_i h
    rw [coverage_swap]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (show a ≤ b by omega)
    rw [Nat.add_sub_cancel_left]
    exact coverage_table_right a k v u (by omega) hv₁ hv₂ hu₁ hu₂

theorem coverage_at_most_three (a b u v : ℕ)
    (hab : a ≤ b + 3) (hba : b ≤ a + 3)
    (hu₁ : 2 ≤ u) (hu₂ : u ≤ 4) (hv₁ : 2 ≤ v) (hv₂ : v ≤ 4) :
    coverage a b u v ≤ 3 := by
  rw [coverage_table a b u v hab hba hu₁ hu₂ hv₁ hv₂]
  unfold entry evenBit
  repeat' first | omega | split

theorem coverage_far_at_least_two (a b : ℕ)
    (hab : a ≤ b + 3) (hba : b ≤ a + 3) :
    2 ≤ coverage a b 4 4 := by
  rw [coverage_table a b 4 4 hab hba (by decide) (by decide) (by decide) (by decide)]
  unfold entry evenBit
  repeat' first | omega | split

theorem coverage_positive (a b u v : ℕ)
    (hab : a ≤ b + 3) (hba : b ≤ a + 3)
    (hu₁ : 2 ≤ u) (hu₂ : u ≤ 4) (hv₁ : 2 ≤ v) (hv₂ : v ≤ 4) :
    1 ≤ coverage a b u v := by
  rw [coverage_table a b u v hab hba hu₁ hu₂ hv₁ hv₂]
  unfold entry evenBit
  repeat' first | omega | split

#print axioms coverage_positive
#print axioms coverage_table
#print axioms coverage_at_most_three
#print axioms coverage_far_at_least_two
end Graffiti189SixCentre
