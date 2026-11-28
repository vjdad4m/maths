import Std
import Lean

namespace BadScienceSix

def signed (u : Nat) : Int := if u % 2 = 0 then 1 else -1

def dot (a b c d e f : Nat) (i : Nat) : Int :=
  a + signed i * b + signed (i / 2) * c + signed (i / 4) * d +
    signed (i / 8) * e + signed (i / 16) * f

def norm2 (a b c d e f : Nat) : Nat :=
  a*a+b*b+c*c+d*d+e*e+f*f

def upperSq (k : Nat) : Nat :=
  [0,6,20,38,64,86,116,150,192,214,244,278][k]?.getD 0

def insertDesc (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x ≥ y then x :: y :: ys else y :: insertDesc x ys

def projectionSum (k a b c d e f : Nat) : Nat :=
  (((List.range 32).map (fun i => (dot a b c d e f i).natAbs)).foldl
    (fun l v => (insertDesc v l).take k) []).foldl (· + ·) 0

-- Enumerate the sorted absolute coordinates of a sum of k signed cube points.
def check (k : Nat) : Bool :=
  let r := List.range (k / 2 + 1)
  r.all fun a =>
    r.all fun b => a > b ||
    (r.all fun c => b > c ||
    (r.all fun d => c > d ||
    (r.all fun e => d > e ||
    (r.all fun f => e > f ||
      let v := fun x => 2*x + k%2
      let q := norm2 (v a) (v b) (v c) (v d) (v e) (v f)
      q ≤ upperSq k || q > projectionSum k (v a) (v b) (v c) (v d) (v e) (v f)))))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem certificate (k : Fin 12) : check k.val = true := by
  have h : k.val = 0 ∨ k.val = 1 ∨ k.val = 2 ∨ k.val = 3 ∨
      k.val = 4 ∨ k.val = 5 ∨ k.val = 6 ∨ k.val = 7 ∨
      k.val = 8 ∨ k.val = 9 ∨ k.val = 10 ∨ k.val = 11 := by omega
  rcases h with h|h|h|h|h|h|h|h|h|h|h|h <;> rw [h] <;> decide +kernel

theorem bound_of_support (k : Fin 12) (a b c d e f : Nat)
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) (hde : d ≤ e) (hef : e ≤ f)
    (hfk : f ≤ k.val / 2)
    (hs :
      let v := fun x => 2*x + k.val%2
      norm2 (v a) (v b) (v c) (v d) (v e) (v f) ≤
        projectionSum k.val (v a) (v b) (v c) (v d) (v e) (v f)) :
    let v := fun x => 2*x + k.val%2
    norm2 (v a) (v b) (v c) (v d) (v e) (v f) ≤ upperSq k.val := by
  have cert := certificate k
  simp only [check, List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq] at cert
  have h := cert a (by omega) b (by omega)
  rcases h with h | h
  · omega
  rcases h c (by omega) with h | h
  · omega
  rcases h d (by omega) with h | h
  · omega
  rcases h e (by omega) with h | h
  · omega
  rcases h f (by omega) with h | h
  · omega
  rcases h with h | h
  · exact h
  · exact False.elim ((Nat.not_lt_of_ge hs) h)

def units (k : Nat) : Nat := 1464 * k + 2143

theorem chord_arithmetic (k : Fin 12) :
    k.val = 4 ∨ k.val = 8 ∨ 1000000 * upperSq k.val ≤ units k.val ^ 2 := by
  have h : k.val = 0 ∨ k.val = 1 ∨ k.val = 2 ∨ k.val = 3 ∨
      k.val = 4 ∨ k.val = 5 ∨ k.val = 6 ∨ k.val = 7 ∨
      k.val = 8 ∨ k.val = 9 ∨ k.val = 10 ∨ k.val = 11 := by omega
  rcases h with h|h|h|h|h|h|h|h|h|h|h|h <;> rw [h] <;> decide

-- Numerators of six rows. Rows 0–1 have norm sqrt(3), others norm 2.
def witnessRows : List (Nat × (Int × Int × Int × Int × Int × Int)) :=
  [(3, (1,1,1,0,0,0)), (3, (1,1,-1,0,0,0)),
   (4, (1,-1,1,1,0,0)), (4, (1,-1,1,-1,0,0)),
   (4, (1,-1,-1,1,0,0)), (4, (1,-1,-1,-1,0,0))]

def witnessRowSq (x : Int × Int × Int × Int × Int × Int) (i : Nat) : Nat :=
  let (a,b,c,d,e,f) := x
  let u := a + signed i * b + signed (i/2)*c + signed (i/4)*d +
    signed (i/8)*e + signed (i/16)*f
  u.natAbs ^ 2

-- Multiply the squared normalized values by 12 to keep the check integral.
def witnessSq12 (i : Nat) : Nat :=
  (witnessRows.map (fun (m, x) => 12 / m * witnessRowSq x i)).foldl max 0

theorem witness_counts :
    ((List.range 32).filter (fun i => witnessSq12 i = 36)).length = 16 ∧
    ((List.range 32).filter (fun i => witnessSq12 i = 48)).length = 16 := by
  decide +kernel

#print axioms bound_of_support
#print axioms chord_arithmetic
#print axioms witness_counts
end BadScienceSix
