import Mathlib.Logic.Equiv.Fin.Basic
namespace Graffiti189LongestPath.Layer24Numbering
abbrev Kind := Fin 3
def childCount (m : Kind) : ℕ := if m=0 then 12 else 11
def shortIndex (m : Kind) (t : ℕ) : ℕ := if m=1 then t-1 else 1
def cap (t : ℕ) : ℕ := 7-t
def childCap (m : Kind) (t i : ℕ) : ℕ :=
  if m≠0 ∧ i=shortIndex m t then cap t-1 else cap t
def hole (m : Kind) (t : ℕ) : ℕ := (shortIndex m t + 1)*cap t-1
def rawSlot (m : Kind) (t j : ℕ) : ℕ :=
  if m=0 ∨ j<hole m t then j else j+1
def owner (m : Kind) (t j : ℕ) : ℕ := rawSlot m t j / cap t
def cell (m : Kind) (t j : ℕ) : ℕ := rawSlot m t j % cap t
def childHas (m : Kind) (t i j : ℕ) : Prop :=
  owner m t j=i ∨ (m=2 ∧ i=1 ∧ rawSlot m t j=cap t-1)
def firstChild (m : Kind) (t i j : ℕ) : Prop :=
  owner m t j=i ∧ cell m t j=0
def fullSelector (m : Kind) (t i : ℕ) : Prop :=
  m≠1 ∨ i≠shortIndex m t
instance (m : Kind) (t i j : ℕ) : Decidable (childHas m t i j) := by
  unfold childHas; infer_instance
instance (m : Kind) (t i j : ℕ) : Decidable (firstChild m t i j) := by
  unfold firstChild; infer_instance
instance (m : Kind) (t i : ℕ) : Decidable (fullSelector m t i) := by
  unfold fullSelector; infer_instance
end Graffiti189LongestPath.Layer24Numbering
