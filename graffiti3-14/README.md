# Graffiti³ #14

[Davila’s Graffiti³ preprint](https://doi.org/10.21203/rs.3.rs-8493329/v1).

## #14: phi(n) ≥ 2 tau(n) − 8 (true and sharp)

For a prime p and exponent a≥1 set f(p,a)=phi(p^a)/tau(p^a)=(p−1)p^(a−1)/(a+1). This is increasing in a: the ratio of successive terms is p(a+1)/(a+2)>1. Always f(2,a)≥1/2, f(3,a)≥1, and f(p,a)≥2 for p≥5. Consequently phi(n)/tau(n)≥2 unless n belongs to the following finite set: n=2^a 3^b u with 0≤a≤4, 0≤b≤2, u∈{1,5,7}. Indeed:
- a prime p≥11 contributes at least 5, so even a 1/2 factor cannot make the product less than 2;
- having both 5 and 7 contributes at least 2·3, and either one to exponent at least 2 contributes at least 20/3, again enough;
- exponent ≥5 at 2 contributes at least 16/6, and exponent ≥3 at 3 contributes at least 18/4 (enough even after multiplying by 1/2).

The finite remainder has just 45 triples. The axiom-free Lean decision in Certificates.lean establishes the bound on these using the exact prime-factor formulas. Independent gcd/divisor enumeration in certify.py confirms the maximum deficit 2 tau(n)−phi(n) is 8, attained exactly at n=12,24,30,60.

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
