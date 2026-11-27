import ResidualProfile

namespace Graffiti199Depleted.Catalogue.FourShoreModel

/-- The six possible edges on four explicitly labeled vertices. -/
abbrev Mask := Fin 6 → Bool

def low : Fin 6 → Fin 4 := ![0,0,0,1,1,2]
def high : Fin 6 → Fin 4 := ![1,2,3,2,3,3]

def edge (m : Mask) (i j : Fin 4) : Bool :=
  match min i.val j.val, max i.val j.val with
  | 0,1 => m 0
  | 0,2 => m 1
  | 0,3 => m 2
  | 1,2 => m 3
  | 1,3 => m 4
  | 2,3 => m 5
  | _,_ => false

def connectedCuts (m : Mask) : Prop :=
  ∀ S : Finset (Fin 4), S.Nonempty → S ≠ Finset.univ →
    ∃ i ∈ S, ∃ j ∉ S, edge m i j = true

def internalDegree (m : Mask) (i : Fin 4) :=
  (Finset.univ.filter (fun j : Fin 4 => edge m i j = true)).card

def ends (m : Mask) (i j : Fin 4) : Prop :=
  ∃ x y : Fin 4, [i,x,y,j].Nodup ∧
    edge m i x = true ∧ edge m x y = true ∧ edge m y j = true

def isClaw (m : Mask) : Prop :=
  ∃ c : Fin 4, (∀ i, i ≠ c → edge m c i = true) ∧
    ∀ i j, i ≠ c → j ≠ c → edge m i j = false

def allPairs (m : Mask) : Prop := ∀ x y, x ≠ y → ends m x y

def leafPair (m : Mask) : Prop :=
  ∃ x y, internalDegree m x ≤ 1 ∧ internalDegree m y ≤ 2 ∧ ends m x y

def dominantPair (m : Mask) : Prop :=
  ∃ x y, internalDegree m x ≤ 2 ∧ internalDegree m y ≤ 2 ∧ ends m x y ∧
    ∀ z, z ≠ x → z ≠ y → ends m x z ∨ ends m y z

instance (m : Mask) : Decidable (connectedCuts m) := inferInstanceAs
  (Decidable (∀ S : Finset (Fin 4), S.Nonempty → S ≠ Finset.univ →
    ∃ i ∈ S, ∃ j ∉ S, edge m i j = true))
instance (m : Mask) (i j : Fin 4) : Decidable (ends m i j) := inferInstanceAs
  (Decidable (∃ x y : Fin 4, [i,x,y,j].Nodup ∧
    edge m i x = true ∧ edge m x y = true ∧ edge m y j = true))
instance (m : Mask) : Decidable (isClaw m) := inferInstanceAs
  (Decidable (∃ c : Fin 4, (∀ i, i ≠ c → edge m c i = true) ∧
    ∀ i j, i ≠ c → j ≠ c → edge m i j = false))
instance (m : Mask) : Decidable (allPairs m) := inferInstanceAs
  (Decidable (∀ x y, x ≠ y → ends m x y))
instance (m : Mask) : Decidable (leafPair m) := inferInstanceAs
  (Decidable (∃ x y, internalDegree m x ≤ 1 ∧ internalDegree m y ≤ 2 ∧ ends m x y))
instance (m : Mask) : Decidable (dominantPair m) := inferInstanceAs
  (Decidable (∃ x y, internalDegree m x ≤ 2 ∧ internalDegree m y ≤ 2 ∧ ends m x y ∧
    ∀ z, z ≠ x → z ≠ y → ends m x z ∨ ends m y z))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 10000000 in
theorem connected_model_profile :
    ∀ m : Mask, connectedCuts m → isClaw m ∨ allPairs m ∨ leafPair m ∨ dominantPair m := by
  decide +kernel

#print axioms connected_model_profile

end Graffiti199Depleted.Catalogue.FourShoreModel
