import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.VecNotation

namespace Graffiti384b.T11TenNormalize
open Finset
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

abbrev Label := Fin 10

def clique : Finset Label := {1,2,3}

def diamond (k : Fin 4) : Finset Label :=
  (![ {5,6,7}, {1,5,6}, {1,5,6}, {1,2,5} ] : Fin 4 → Finset Label) k

def missing (k : Fin 4) : Finset Label :=
  (![ {5,6}, {1,5}, {5,6}, {1,5} ] : Fin 4 → Finset Label) k

def motif (k : Fin 4) (i j : Label) : Option Bool :=
  if i=j then some false else
  if i=0 then some (decide (j∈clique)) else
  if j=0 then some (decide (i∈clique)) else
  if i=4 then some (decide (j∈diamond k)) else
  if j=4 then some (decide (i∈diamond k)) else
  if i∈clique ∧ j∈clique then some true else
  if i∈diamond k ∧ j∈diamond k then some (decide (({i,j} : Finset Label) ≠ missing k))
  else none

def allowedCuts (k : Fin 4) : Finset Nat :=
  (![ {307,355,403,419}, {181,213,229,403,419,451}, {181,229,403,419}, {121,211,213,227,229} ] :
    Fin 4 → Finset Nat) k

def opposite (A : Finset Label) (r w : Label) : Prop := (w∈A ↔ r∉A)
instance (A : Finset Label) (r w : Label) : Decidable (opposite A r w) := by
  unfold opposite
  infer_instance

end Graffiti384b.T11TenNormalize
