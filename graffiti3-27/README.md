# Graffiti³ #27

[Davila’s Graffiti³ preprint](https://doi.org/10.21203/rs.3.rs-8493329/v1).

## #27: Sylow orders and class count (false)

The printed claim is that a finite p-group G has at least (7/16)·abs(|G/G′|−|Syl₂(G)|)−4 conjugacy classes.

Write D_64=<r,s | r^32=s²=1, srs=r⁻¹>. Its rotations form 17 classes, with 1 and r^16 singleton and all other rotations paired with their inverse. Reflections form exactly two classes by the parity of the power of r. Thus k=19. The derived subgroup is <r²>, since the commutator of s and r is r^±2 and quotienting by <r²> gives an abelian group; the quotient has order 4. The 2-Sylow is the whole group, so the proposed right side is (7/16)·|4−64|−4=89/4>19. More generally, for a dihedral group of order q which is a power of two at least 64, the class count is q/4+3 and the stated lower bound is 7(q−4)/16−4. Their difference (bound minus class count) is (3q−140)/16 and is positive for all such q. Thus witnesses exist far beyond any fixed snapshot cutoff.

## Verification scope

The finite arithmetic is checked in Lean 4.19.0. The general argument is written above.

<details>
<summary>Certificates.lean</summary>

```lean
import Std
namespace GraffitiThree

-- #14: finite remainder after the prime-power ratios in NOTES.md.
/-- Euler factor of a prime raised to exponent a, also valid for a=0. -/
def factorPhi (p : Nat) : Nat → Nat
  | 0 => 1
  | a+1 => (p-1) * p^a

def goodSmall (a b u : Nat) : Bool :=
  decide (2 * (a+1) * (b+1) * (if u = 1 then 1 else 2)
     ≤ factorPhi 2 a * factorPhi 3 b * (if u = 1 then 1 else u-1) + 8)

theorem totient_finite_remainder :
    ((List.range 5).all fun a =>
      (List.range 3).all fun b => [1,5,7].all (goodSmall a b)) = true := by decide

-- #9: conflicting precedence conditions for a reversed endpoint pair.
theorem no_interchain_reversal (bJ aNext aK bNext : Nat)
    (hab : bJ < aNext) (haa : aNext ≤ aK)
    (hba : aK < bNext) (hbb : bNext ≤ bJ) : False := by omega

-- #15(a), #21, #22, #27: exact numeric finishes, not the group proof.
theorem a5D8_meets_separator : 2 ≤ 4*25 ∧ 9*2*480 ≤ (4*25-2)^2 := by decide
theorem ut6_falls_below_21 : 275 < (1024 : Nat)-32+1 := by decide
theorem ut6_falls_below_22 : 275 < (1024 : Nat)-8+1 := by decide
theorem dihedral64_falls_below_27 : 16*(19+4) < 7*((64 : Nat)-4) := by decide

#print axioms totient_finite_remainder
#print axioms no_interchain_reversal
#print axioms a5D8_meets_separator
#print axioms ut6_falls_below_21
#print axioms ut6_falls_below_22
#print axioms dihedral64_falls_below_27
end GraffitiThree
```

</details>

AI-assisted work shared for review. No priority claim is made.
