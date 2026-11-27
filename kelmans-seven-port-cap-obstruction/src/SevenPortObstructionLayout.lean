import ThetaLocalRoute
import SevenPortObstruction

namespace KelmansCactus.AtomicBridge.SevenPortObstruction
open ThetaExteriorFixture (es)
open ThetaLocalRoute (Mode Ring route)

def mode (i : Ear) : Mode := ⟨i.val / 2,by have hi := i.isLt; omega⟩
def old (j : Ring) : Point := if j=1 then 7 else if j=2 then 8 else if j=4 then 9 else 11
def C (i : Ear) (j : Nat) : Point := (contacts i)[j]?.getD 0

def outsideAdj (a b : Point) : Prop :=
  7≤a.val ∧ 7≤b.val ∧ ((a,b)∈es.map (fun (v,w)=>(lift v,lift w)) ∨
       (b,a)∈es.map (fun (v,w)=>(lift v,lift w)))

instance (a b : Point) : Decidable (outsideAdj a b) := by
  unfold outsideAdj
  infer_instance

/-- For each possible oriented ear, the four retained old labels are exactly
the ones obtained by the specified theta dihedral route, and the
three new labels are all surviving exterior incidences of the ear. -/
theorem exact_ear_contacts (i : Ear) :
    x i = old (route (mode i) 1) ∧
    C i 0 = old (route (mode i) 2) ∧ C i 1 = old (route (mode i) 4) ∧
    C i 2 = 10 ∧ C i 3 = old (route (mode i) 5) ∧
    outsideAdj (x i) (y i) ∧
    (∀ v : Point,outsideAdj (x i) v ∧ v≠y i ↔ v=C i 4) ∧
    (∀ v : Point,outsideAdj (y i) v ∧ v≠x i ↔ v=C i 5∨v=C i 6) ∧
    (C i 5 ≠ C i 6) := by
  fin_cases i <;> decide

#print axioms exact_ear_contacts
end KelmansCactus.AtomicBridge.SevenPortObstruction
