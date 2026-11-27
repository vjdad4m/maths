import TreeBudget

namespace Graffiti199Depleted.CompactOmission

abbrev Row := Bool × Bool × Bool × Bool × Bool × Bool × Bool

def flags (r : Row) : Fin 7 → Bool := ![r.1,r.2.1,r.2.2.1,r.2.2.2.1,r.2.2.2.2.1,r.2.2.2.2.2.1,r.2.2.2.2.2.2]

def mask (r : Row) : ℕ :=
  (if flags r 0 then 1 else 0) + (if flags r 1 then 2 else 0) +
  (if flags r 2 then 4 else 0) + (if flags r 3 then 8 else 0) +
  (if flags r 4 then 16 else 0) + (if flags r 5 then 32 else 0) +
  (if flags r 6 then 64 else 0)

def hasCubicSlot (r : Row) : Bool :=
  (!flags r 4 && !flags r 5) || (!flags r 0 && !flags r 6) || (!flags r 1 && !flags r 3)

def allowed (r : Row) : Bool := ([38,46,54,62,79,117] : List ℕ).contains (mask r)

def directed (r : Row) (a b : Fin 8) : Bool :=
  match a.val,b.val with
  | 0,1 | 1,2 | 2,3 | 3,4 | 4,5 | 5,6 | 1,7 | 3,7 | 5,7 => true
  | 0,3 => flags r 0
  | 0,5 => flags r 1
  | 0,6 => flags r 2
  | 2,5 => flags r 3
  | 1,4 => flags r 4
  | 1,6 => flags r 5
  | 3,6 => flags r 6
  | _,_ => false

def adjacent (r : Row) (a b : Fin 8) : Bool := directed r a b || directed r b a

/-- Six distinct labels ordered by distance from a root of their induced tree. -/
def treeOrder : ℕ → Fin 6 → Fin 8
  | 0 => ![0,1,2,3,4,5]
  | 1 => ![0,1,3,4,5,6]
  | 2 => ![0,1,5,2,6,3]
  | 3 => ![0,1,5,2,4,6]
  | 4 => ![0,1,2,3,4,5]
  | 5 => ![0,1,6,2,5,4]
  | 6 => ![0,1,6,2,3,4]
  | 7 => ![1,2,3,4,5,6]
  | 8 => ![0,1,2,3,5,6]
  | 9 => ![0,1,2,5,4,6]
  | 10 => ![0,1,5,4,6,3]
  | 11 => ![0,5,2,4,6,7]
  | 12 => ![0,1,6,2,3,4]
  | 13 => ![0,3,6,2,4,7]
  | 14 => ![0,1,6,2,3,4]
  | 15 => ![0,3,6,2,4,7]
  | 16 => ![0,1,2,4,5,6]
  | 17 => ![0,1,2,4,5,6]
  | 18 => ![0,1,5,2,6,3]
  | 20 => ![0,1,6,2,5,3]
  | 21 => ![0,1,6,2,4,7]
  | 22 => ![0,1,6,2,4,7]
  | 24 => ![0,1,2,3,5,6]
  | 26 => ![0,5,2,4,6,7]
  | 28 => ![0,1,6,2,4,7]
  | 30 => ![0,1,6,2,4,7]
  | 32 => ![0,1,2,3,4,5]
  | 33 => ![0,1,2,6,5,4]
  | 34 => ![0,1,2,6,3,4]
  | 36 => ![0,1,2,3,4,5]
  | 37 => ![0,1,2,7,5,4]
  | 40 => ![0,1,2,6,3,4]
  | 42 => ![0,1,2,6,3,4]
  | 44 => ![0,6,5,2,4,7]
  | 48 => ![0,1,2,6,3,5]
  | 49 => ![0,3,2,4,5,6]
  | 50 => ![0,5,4,6,3,2]
  | 52 => ![0,6,5,4,3,2]
  | 53 => ![0,3,6,2,4,7]
  | 56 => ![0,1,2,4,6,7]
  | 58 => ![0,1,2,4,6,7]
  | 60 => ![0,6,5,2,4,7]
  | 64 => ![0,1,2,3,4,5]
  | 65 => ![0,1,2,7,5,4]
  | 66 => ![0,1,2,3,4,6]
  | 67 => ![0,1,5,2,4,6]
  | 68 => ![0,1,2,3,4,5]
  | 69 => ![0,1,6,2,5,4]
  | 70 => ![0,6,3,2,4,7]
  | 71 => ![1,2,7,5,4,6]
  | 72 => ![0,1,2,3,4,6]
  | 73 => ![0,1,2,5,4,6]
  | 74 => ![0,1,2,3,4,6]
  | 75 => ![0,3,2,4,6,7]
  | 76 => ![0,6,3,2,4,7]
  | 77 => ![0,6,5,2,4,7]
  | 78 => ![0,6,3,2,4,7]
  | 80 => ![0,1,2,3,6,5]
  | 81 => ![0,1,2,4,5,6]
  | 84 => ![0,1,6,2,4,7]
  | 85 => ![0,1,6,2,4,7]
  | 96 => ![0,1,2,3,4,5]
  | 97 => ![0,1,2,6,5,4]
  | 100 => ![0,1,2,3,4,5]
  | 101 => ![0,1,2,7,5,4]
  | 112 => ![0,1,2,4,6,7]
  | 113 => ![0,1,2,4,6,7]
  | 116 => ![0,6,3,2,4,7]
  | _ => ![0,1,2,3,4,5]

set_option maxHeartbeats 3500000 in
set_option maxRecDepth 4096 in
theorem coverage : ∀ r : Row, hasCubicSlot r = true →
    allowed r = true ∨
    (∀ i j : Fin 6, treeOrder (mask r) i = treeOrder (mask r) j → i = j) ∧
      ∀ i : Fin 6, i ≠ 0 → ∃ j : Fin 6,
        adjacent r (treeOrder (mask r) i) (treeOrder (mask r) j) = true ∧ j < i ∧
        ∀ k : Fin 6, adjacent r (treeOrder (mask r) i) (treeOrder (mask r) k) = true →
          k < i → k = j := by decide

set_option maxRecDepth 4096 in
theorem allowed_outer_chord : ∀ r : Row, allowed r = true → adjacent r 0 6 = true := by decide

#print axioms coverage

end Graffiti199Depleted.CompactOmission
