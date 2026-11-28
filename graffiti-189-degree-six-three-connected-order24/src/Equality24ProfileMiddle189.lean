import SixLayer24SlotNumbers189
import Mathlib.Combinatorics.SimpleGraph.Finite

namespace Graffiti189LongestPath.Equality24Profile
open Finset SimpleGraph Layer24Numbering
abbrev Vert := Fin 24
def inA (i : Vert) : Prop := 1≤i.val ∧ i.val<7
def inB (b : ℕ) (i : Vert) : Prop := 7≤i.val ∧ i.val<7+b
def inC (m : Kind) (b : ℕ) (i : Vert) : Prop := 7+b≤i.val ∧ i.val<7+b+childCount m
def selected (t : ℕ) (i : Vert) : Prop := 1≤i.val ∧ i.val≤t
def marked (t : ℕ) (i : Vert) : Prop := 7≤i.val ∧ i.val<7+t
def layer (m : Kind) (b : ℕ) (i : Vert) : ℕ :=
  if i.val=0 then 0 else if i.val<7 then 1 else
    if i.val<7+b then 2 else if i.val<7+b+childCount m then 3 else 4
instance (i : Vert) : Decidable (inA i) := by unfold inA; infer_instance
instance (b : ℕ) (i : Vert) : Decidable (inB b i) := by unfold inB; infer_instance
instance (m : Kind) (b : ℕ) (i : Vert) : Decidable (inC m b i) := by unfold inC; infer_instance
instance (t : ℕ) (i : Vert) : Decidable (selected t i) := by unfold selected; infer_instance
instance (t : ℕ) (i : Vert) : Decidable (marked t i) := by unfold marked; infer_instance
def markedOf (i : Vert) : Vert := ⟨(i.val+6)%24,Nat.mod_lt _ (by decide)⟩
def forcedAdj (m : Kind) (t b : ℕ) (i j : Vert) : Option Bool :=
  if i.val≥j.val then none
  else if i=0 then some (decide (inA j))
  else if layer m b i + 1 < layer m b j then some false
  else if selected t i ∧ inA j ∧ ¬selected t j ∧ fullSelector m t (i.val-1) then some true
  else if selected t i ∧ marked t j then some (decide (j=markedOf i))
  else if marked t i ∧ inC m b j then
    if ¬childHas m t (i.val-7) (j.val-(7+b)) then some false
    else if firstChild m t (i.val-7) (j.val-(7+b)) then some true else none
  else none
def forcedD2 (m : Kind) (t b : ℕ) (i j : Vert) : Option Bool :=
  if i=0 then some (decide (inB b j))
  else if selected t i then
    if inC m b j then some (decide (childHas m t (i.val-1) (j.val-(7+b))))
    else if fullSelector m t (i.val-1) ∧
      ¬((selected t j ∧ j≠i) ∨ (marked t j ∧ j≠markedOf i)) then some false
    else none
  else none
def TwoStep (G : SimpleGraph Vert) (i j : Vert) : Prop :=
  i≠j ∧ ¬G.Adj i j ∧ ∃ k,G.Adj i k ∧ G.Adj k j
instance decTwoStep (G : SimpleGraph Vert) [DecidableRel G.Adj] :
    DecidableRel (TwoStep G) := fun i j => by unfold TwoStep; infer_instance
def Shadow (G : SimpleGraph Vert) [DecidableRel G.Adj] (i : Vert) : Finset Vert :=
  univ.filter (TwoStep G i)
structure Model (G : SimpleGraph Vert) [DecidableRel G.Adj] (m : Kind) (t b : ℕ) : Prop where
  forcedEdge : ∀ i j q,forcedAdj m t b i j=some q → (G.Adj i j ↔ q=true)
  forcedShadow : ∀ i j q,forcedD2 m t b i j=some q → (TwoStep G i j ↔ q=true)
  cross : ∀ i j,selected t i → selected t j → i≠j → fullSelector m t (i.val-1) →
    TwoStep G i (markedOf j) → G.Adj i j
  cap : ∀ i,(Shadow G i).card≤6
  pair : ∀ i j,i≠j → 6≤G.degree i ∨ 6≤G.degree j
  parent : ∀ i,i≠0 → ∃ j,layer m b j+1=layer m b i ∧ G.Adj i j
theorem twoStep_symm {G : SimpleGraph Vert} {i j : Vert} :
    TwoStep G i j ↔ TwoStep G j i := by
  constructor <;> rintro ⟨ne,no,k,e₁,e₂⟩
  · exact ⟨ne.symm,(fun e=>no e.symm),k,e₂.symm,e₁.symm⟩
  · exact ⟨ne.symm,(fun e=>no e.symm),k,e₂.symm,e₁.symm⟩
end Graffiti189LongestPath.Equality24Profile
