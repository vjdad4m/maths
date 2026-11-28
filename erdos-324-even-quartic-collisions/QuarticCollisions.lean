import Lean

/-! Explicit obstructions for the even-quartic family in Erdős Problem #324.
The general existence question is not settled by these results. -/

namespace Erdos324

def evenQuartic (c x : Nat) : Nat := x^4 + c*x^2

def HasCollision (f : Nat → Nat) : Prop :=
  ∃ a b u v : Nat, a < b ∧ u < v ∧ (a,b) ≠ (u,v) ∧ f a + f b = f u + f v

theorem evenQuartic_scale (c k x : Nat) :
    evenQuartic (c*k^2) (k*x) = k^4 * evenQuartic c x := by
  unfold evenQuartic
  simp only [Nat.mul_pow, Nat.mul_add, Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
  ac_rfl

theorem scaled_collision (c k : Nat) (hk : 0 < k)
    (h : HasCollision (evenQuartic c)) :
    HasCollision (evenQuartic (c*k^2)) := by
  obtain ⟨a,b,u,v,hab,huv,hn,hs⟩ := h
  refine ⟨k*a,k*b,k*u,k*v, Nat.mul_lt_mul_of_pos_left hab hk,
    Nat.mul_lt_mul_of_pos_left huv hk, ?_, ?_⟩
  · intro eq
    have e₁ := congrArg Prod.fst eq
    have e₂ := congrArg Prod.snd eq
    exact hn (Prod.ext (Nat.eq_of_mul_eq_mul_left hk e₁) (Nat.eq_of_mul_eq_mul_left hk e₂))
  · simp only [evenQuartic_scale, ← Nat.mul_add, hs]

theorem coefficients_1_through_32 (c : Nat) (hl : 1 ≤ c) (hh : c ≤ 32) :
    HasCollision (evenQuartic c) := by
  have hc : c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 ∨ c = 7 ∨ c = 8 ∨ c = 9 ∨ c = 10 ∨ c = 11 ∨ c = 12 ∨ c = 13 ∨ c = 14 ∨ c = 15 ∨ c = 16 ∨ c = 17 ∨ c = 18 ∨ c = 19 ∨ c = 20 ∨ c = 21 ∨ c = 22 ∨ c = 23 ∨ c = 24 ∨ c = 25 ∨ c = 26 ∨ c = 27 ∨ c = 28 ∨ c = 29 ∨ c = 30 ∨ c = 31 ∨ c = 32 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨37,50,22,53,by decide,by decide,by decide,by decide⟩
  · exact ⟨7,8,0,9,by decide,by decide,by decide,by decide⟩
  · exact ⟨0,16,11,15,by decide,by decide,by decide,by decide⟩
  · exact ⟨16,25,1,26,by decide,by decide,by decide,by decide⟩
  · exact ⟨6,28,17,27,by decide,by decide,by decide,by decide⟩
  · exact ⟨34,43,23,46,by decide,by decide,by decide,by decide⟩
  · exact ⟨2,18,12,17,by decide,by decide,by decide,by decide⟩
  · exact ⟨14,16,0,18,by decide,by decide,by decide,by decide⟩
  · exact ⟨2,20,13,19,by decide,by decide,by decide,by decide⟩
  · exact ⟨10,13,5,14,by decide,by decide,by decide,by decide⟩
  · exact ⟨55,95,38,97,by decide,by decide,by decide,by decide⟩
  · exact ⟨22,30,0,32,by decide,by decide,by decide,by decide⟩
  · exact ⟨1,11,8,10,by decide,by decide,by decide,by decide⟩
  · exact ⟨17,21,5,23,by decide,by decide,by decide,by decide⟩
  · exact ⟨4,104,73,97,by decide,by decide,by decide,by decide⟩
  · exact ⟨2,15,12,13,by decide,by decide,by decide,by decide⟩
  · exact ⟨32,35,3,40,by decide,by decide,by decide,by decide⟩
  · exact ⟨21,24,0,27,by decide,by decide,by decide,by decide⟩
  · exact ⟨6,7,0,8,by decide,by decide,by decide,by decide⟩
  · exact ⟨6,7,1,8,by decide,by decide,by decide,by decide⟩
  · exact ⟨209,405,6,412,by decide,by decide,by decide,by decide⟩
  · exact ⟨4,15,12,13,by decide,by decide,by decide,by decide⟩
  · exact ⟨1,13,9,12,by decide,by decide,by decide,by decide⟩
  · exact ⟨31,48,3,50,by decide,by decide,by decide,by decide⟩
  · exact ⟨3,32,24,29,by decide,by decide,by decide,by decide⟩
  · exact ⟨18,23,2,25,by decide,by decide,by decide,by decide⟩
  · exact ⟨33,45,0,48,by decide,by decide,by decide,by decide⟩
  · exact ⟨24,34,4,36,by decide,by decide,by decide,by decide⟩
  · exact ⟨11,15,6,16,by decide,by decide,by decide,by decide⟩
  · exact ⟨1,62,43,58,by decide,by decide,by decide,by decide⟩
  · exact ⟨5,15,12,13,by decide,by decide,by decide,by decide⟩
  · exact ⟨3,20,15,18,by decide,by decide,by decide,by decide⟩

theorem coefficients_1_through_32_times_square (c k : Nat) (hl : 1 ≤ c)
    (hh : c ≤ 32) (hk : 0 < k) : HasCollision (evenQuartic (c*k^2)) :=
  scaled_collision c k hk (coefficients_1_through_32 c hl hh)

#print axioms coefficients_1_through_32
#print axioms coefficients_1_through_32_times_square
end Erdos324

