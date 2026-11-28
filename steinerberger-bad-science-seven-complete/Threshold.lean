import Std
import Lean

namespace BadScienceSeven

def signed (u : Nat) : Int := if u % 2 = 0 then 1 else -1

def dot7 (a b c d e f g i : Nat) : Int :=
  a + signed i * b + signed (i/2)*c + signed (i/4)*d +
   signed (i/8)*e + signed (i/16)*f + signed (i/32)*g

def norm7 (a b c d e f g : Nat) : Nat := a*a+b*b+c*c+d*d+e*e+f*f+g*g

def budget7 (k a b c d e f g : Nat) : Nat :=
  let t := if k < 14 then 26 else 30
  k*t + ((List.range 64).map (fun i => (dot7 a b c d e f g i).natAbs-t)).sum

def lineSq (k : Nat) : Nat :=
  if k=8 then 256 else if k=16 then 768 else (1464*k+4286)^2/1000000

def checkPrefix (k a : Nat) : Bool :=
  let r := List.range (k / 2 + 1)
  r.all fun b => a > b ||
    (r.all fun c => b > c ||
    (r.all fun d => c > d ||
    (r.all fun e => d > e ||
    (r.all fun f => e > f ||
    (r.all fun g => f > g ||
      let v := fun x => 2*x + k%2
      let q := norm7 (v a) (v b) (v c) (v d) (v e) (v f) (v g)
      q ≤ lineSq k || q > 64*k ||
        q > budget7 k (v a) (v b) (v c) (v d) (v e) (v f) (v g))))))

theorem sound_prefix (k a b c d e f g : Nat) (ha : checkPrefix k a = true)
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) (hde : d ≤ e)
    (hef : e ≤ f) (hfg : f ≤ g) (hg : g ≤ k / 2)
    (hParseval :
      let v := fun x => 2*x+k%2
      norm7 (v a) (v b) (v c) (v d) (v e) (v f) (v g) ≤ 64*k)
    (hBudget :
      let v := fun x => 2*x+k%2
      norm7 (v a) (v b) (v c) (v d) (v e) (v f) (v g) ≤
        budget7 k (v a) (v b) (v c) (v d) (v e) (v f) (v g)) :
    let v := fun x => 2*x+k%2
    norm7 (v a) (v b) (v c) (v d) (v e) (v f) (v g) ≤ lineSq k := by
  simp only [checkPrefix,List.all_eq_true,List.mem_range,Bool.or_eq_true,decide_eq_true_eq] at ha
  rcases ha b (by omega) with h|h
  · omega
  rcases h c (by omega) with h|h
  · omega
  rcases h d (by omega) with h|h
  · omega
  rcases h e (by omega) with h|h
  · omega
  rcases h f (by omega) with h|h
  · omega
  rcases h g (by omega) with h|h
  · omega
  rcases h with (h|h)|h
  · exact h
  · exact False.elim ((Nat.not_lt_of_ge hParseval) h)
  · exact False.elim ((Nat.not_lt_of_ge hBudget) h)

end BadScienceSeven
