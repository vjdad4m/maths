import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix.PortCertificates

def other (i : Fin 2) : Fin 2 := if i = 0 then 1 else 0
def mate (i : Fin 4) : Fin 4 := ![1,0,3,2] i
def left (i : Fin 4) : Bool := i.val < 2

abbrev pairTwoModel (T : Fin 2 → Fin 4 → Bool) (A : Fin 4 → Bool) : Prop :=
  (∀ i u v, u≠v → T i u=true ∨ T i v=true) ∧
  (∀ u, A u=false → ∀ i,T i u=true) ∧
  (A 0=true ∨ A 1=true) ∧ (A 2=true ∨ A 3=true)

abbrev pairTwoRoute (T : Fin 2 → Fin 4 → Bool) (A : Fin 4 → Bool) : Prop :=
  ∃ x y : Fin 4, ∃ k : Fin 2,
    left x≠left y ∧ A x=true ∧ A y=true ∧
      T k y=true ∧ T k (mate x)=true ∧ T (other k) (mate x)=true

def row3 (a b c : Bool) : Fin 3 → Bool := ![a,b,c]
def row4 (a b c d : Bool) : Fin 4 → Bool := ![a,b,c,d]
def mat24 (a b c d e f g h : Bool) : Fin 2 → Fin 4 → Bool :=
  ![row4 a b c d,row4 e f g h]
def mat33 (a b c d e f g h i : Bool) : Fin 3 → Fin 3 → Bool :=
  ![row3 a b c,row3 d e f,row3 g h i]
def rows33 (a b c : Bool) : Fin 3 → Fin 3 → Bool :=
  ![row3 false a b,row3 a false c,row3 b c false]

set_option maxHeartbeats 100000000
set_option maxRecDepth 32768

theorem pair_two_certificate (a b c d e f g h : Bool) :
    ∀ (x y z w : Bool), pairTwoModel (mat24 a b c d e f g h) (row4 x y z w) →
      pairTwoRoute (mat24 a b c d e f g h) (row4 x y z w) := by
  cases a <;> cases b <;> cases c <;> cases d <;> revert e f g h <;> decide

def yIndex (i : Fin 2) : Fin 3 := if i=0 then 1 else 2

def marks (p : Bool) : Nat := if p then 1 else 0

abbrev oneTwoModel (C T : Fin 3 → Fin 3 → Bool) (A : Fin 2 → Bool) : Prop :=
  (∀ i : Fin 3, 4 ≤ marks (C i 0)+marks (C i 1)+marks (C i 2)+
      marks (T i 0)+marks (T i 1)+marks (T i 2)) ∧ (A 0=true ∨ A 1=true)

abbrev oneTwoRoute (C T : Fin 3 → Fin 3 → Bool) (A : Fin 2 → Bool) : Prop :=
  ∃ y : Fin 2, ∃ i j k : Fin 3, A y=true ∧ i≠j ∧ i≠k ∧ j≠k ∧
    ((T i (yIndex y)=true ∧ C i j=true ∧ C j k=true) ∨
      (T i 0=true ∧ C j k=true ∧ T k (yIndex (other y))=true))

theorem one_two_certificate (p q r : Bool) (a b c d e f g h i : Bool) :
    ∀ (x y : Bool), oneTwoModel (rows33 p q r) (mat33 a b c d e f g h i) ![x,y] →
      oneTwoRoute (rows33 p q r) (mat33 a b c d e f g h i) ![x,y] := by
  cases p <;> cases q <;> cases r <;> revert a b c d e f g h i <;> decide

#print axioms pair_two_certificate
#print axioms one_two_certificate
end Graffiti189LongestPath.CrossSaturation.ThresholdSix.PortCertificates
