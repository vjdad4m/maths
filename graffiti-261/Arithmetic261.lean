import Std
set_option warningAsError true
namespace Graffiti261

/-- Karpov's leaf bound gives x + 6 ≤ 4*L. The exceptional singleton
degree-two set corresponds to (x,L,t)=(2,2,2). -/
theorem arithmetic (n x L t : Nat)
    (hL : 2 ≤ L) (ht : 2 ≤ t)
    (hKarpov : x + 6 ≤ 4*L)
    (hConnectedDomination : n + 2 ≤ L + 2*t)
    (hSmall : t ≤ 3 → n ≤ L+t)
    (hSize : x ≤ 2 ∨ x+2 ≤ n) :
    2*x ≤ t*L := by
  by_cases hx : x ≤ 2
  · have h : 2*2 ≤ t*L := Nat.mul_le_mul ht hL
    omega
  · have hnx : x+2 ≤ n := hSize.resolve_left hx
    by_cases h4 : 4 ≤ L
    · let a := t-2
      let b := L-4
      have ha : t = a+2 := by dsimp [a]; omega
      have hb : L = b+4 := by dsimp [b]; omega
      calc
        2*x ≤ 2*b + 4*a + 8 := by omega
        _ ≤ a*b + (2*b + 4*a + 8) := by omega
        _ = t*L := by
          rw [ha, hb]
          simp only [Nat.add_mul, Nat.mul_add]
          omega
    · have h3 : L = 3 := by omega
      subst L
      by_cases hs : t ≤ 3
      · have h := hSmall hs
        omega
      · omega
#print axioms arithmetic
end Graffiti261
