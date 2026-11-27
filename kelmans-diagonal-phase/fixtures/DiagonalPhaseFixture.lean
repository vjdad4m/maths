import DiagonalPhaseRanks
import Mathlib.Data.List.Chain

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.DiagonalPhaseFixture
open SquareCap (HasFactor)

def diagA : List Board := route [0,1,2,3,4,5]
def diagB : List Board := route [6,7,8,9,10,11]
def cyclicOrder (reverse : Bool) : List Board := diagA ++ (if reverse then diagB.reverse else diagB)
def earOne : List Board := route [10,24,4]
def earTwo : List Board := route [7,25,12,1]
def earThree : List Board := route [2,26,13,14,8]
def earTwelve : List Board := route [9,15,16,17,27,18,19,28,20,21,22,23,29,3]
def interior (l : List Board) : List Board := l.tail.dropLast

def earEnds : Finset Board := (route [1,4,7,10]).toFinset
def bothGaps (i j : ℕ) : ℕ × ℕ := ((j+12-i-1)%12,(i+12-j-1)%12)

def Ear (k : Bool) (l : List Board) : Prop :=
  l.Nodup ∧ l.Chain' pairUnion.Adj ∧ l.head?.getD (decode 0)∈(cyclicOrder k).toFinset ∧
    l.getLast?.getD (decode 0)∈(cyclicOrder k).toFinset
instance (k : Bool) (l : List Board) : Decidable (Ear k l) := by
  unfold Ear
  infer_instance

set_option maxRecDepth 20000 in
theorem ear_geometry (k : Bool) :
    (cyclicOrder k).Nodup ∧ (cyclicOrder k).length=12 ∧
    ((cyclicOrder k).getLast?.getD (decode 0) :: cyclicOrder k).Chain' pairUnion.Adj ∧
    (Ear k earOne ∧ Ear k earTwo ∧ Ear k earThree ∧ Ear k earTwelve) ∧
    ((cyclicOrder k) ++ interior earOne ++ interior earTwo ++
      interior earThree ++ interior earTwelve).Nodup ∧
    ((cyclicOrder k) ++ interior earOne ++ interior earTwo ++
      interior earThree ++ interior earTwelve).toFinset=univ ∧
    (interior earOne).length=1 ∧ (interior earTwo).length=2 ∧
    (interior earThree).length=3 ∧ (interior earTwelve).length=12 := by
  cases k <;> decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 15000 in
theorem phase_geometry (k : Bool) :
    (∀ i : Fin 12,
       (cyclicOrder k)[i.val]! ∈ earEnds ↔ i.val%3=1) ∧
    (∀ i j : Fin 12,i≠j →
      (cyclicOrder k)[i.val]! ∈ earEnds → (cyclicOrder k)[j.val]! ∈ earEnds →
      (bothGaps i.val j.val).1%3=2 ∧ (bothGaps i.val j.val).2%3=2) := by
  have phase : ∀ i : Fin 12,(cyclicOrder k)[i.val]! ∈ earEnds ↔ i.val%3=1 := by
    cases k <;> decide
  have arithmetic : ∀ i j : Fin 12,i≠j → i.val%3=1 → j.val%3=1 →
      (bothGaps i.val j.val).1%3=2 ∧ (bothGaps i.val j.val).2%3=2 := by decide
  exact ⟨phase,fun i j ne hi hj=>arithmetic i j ne ((phase i).mp hi) ((phase j).mp hj)⟩

private def triple (u v w : Nat) : Finset Board := {decode u,decode v,decode w}
private def tiles : Finset (Finset Board) :=
  {triple 14 13 26,
   triple 9 15 16,
   triple 17 27 18,
   triple 19 28 20,
   triple 21 22 23,
   triple 6 7 8,
   triple 1 12 25,
   triple 0 11 5,
   triple 4 24 10,
   triple 2 3 29}

theorem pair_factors : HasFactor pairUnion := by
  refine ⟨tiles,?_,?_,?_⟩
  · change ∀ A ∈ tiles,A.card=3 ∧ ∃ c∈A,∀ x∈A,x≠c → pairUnion.Adj c x
    decide
  · decide
  · decide

#print axioms ear_geometry
#print axioms phase_geometry
#print axioms pair_factors
end KelmansCactus.AtomicBridge.DiagonalPhaseFixture
